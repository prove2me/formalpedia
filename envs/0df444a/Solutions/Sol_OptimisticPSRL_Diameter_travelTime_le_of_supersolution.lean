-- Prove2me | solution 1 for OptimisticPSRL.Diameter.travelTime_le_of_supersolution
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:12:53.978086+00:00
-- url     : https://prove2.me/submissions/13f93f9d-87cc-4b5f-aa0d-932094ba5dbd

import Mathlib
import Definitions.Def_FiniteMDPLearning

set_option autoImplicit false
section VVQ
open BanditAlgorithm NNReal ENNReal MeasureTheory ProbabilityTheory

namespace QQE

open scoped Classical

variable {S A : ℕ}

lemma meas_all {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Finite α]
    (E : Set α) : MeasurableSet E := (Set.toFinite E).measurableSet

lemma mu_succ_apply (M : FiniteMDP S A) (μ0 : MDPStateDistribution S) (π : MDPPolicy S A) (n : ℕ)
    (E : Set (MDPTrajectory S A (n+1))) :
    mdpMeasure M μ0 π (n+1) E = ∫⁻ h, mdpStepKernel M μ0 π n h
      {p | Fin.snoc (α := fun _ => Fin S × Fin A) h p ∈ E} ∂(mdpMeasure M μ0 π n) := by
  rw [mdpMeasure, Measure.map_apply measurable_mdpTrajectorySnoc (meas_all E),
    Measure.compProd_apply (measurable_mdpTrajectorySnoc (meas_all E))]
  rfl


lemma step_gen (M : FiniteMDP S A) (f : Fin S → Fin A) (μ0 : MDPStateDistribution S) (n : ℕ)
    (h : MDPTrajectory S A n) (B : Set (Fin S × Fin A)) (d : MDPStateDistribution S)
    (hd : mdpStateKernel M μ0 n h = d.toMeasure) :
    mdpStepKernel M μ0 (mdpMemorylessDetPolicy f) n h B =
      ∑ s', (d.prob s' : ℝ≥0∞) * (if (s', f s') ∈ B then 1 else 0) := by
  rw [mdpStepKernel, Kernel.compProd_apply (meas_all B), hd, MDPStateDistribution.toMeasure,
    lintegral_finsetSum_measure]
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [lintegral_smul_measure, lintegral_dirac]
  simp only [mdpMemorylessDetPolicy, Kernel.deterministic_apply, smul_eq_mul]
  rw [Measure.dirac_apply' _ (meas_all _)]
  simp [Set.indicator]

lemma step_zero (M : FiniteMDP S A) (f : Fin S → Fin A) (μ0 : MDPStateDistribution S)
    (h : MDPTrajectory S A 0) (B : Set (Fin S × Fin A)) :
    mdpStepKernel M μ0 (mdpMemorylessDetPolicy f) 0 h B =
      ∑ s', (μ0.prob s' : ℝ≥0∞) * (if (s', f s') ∈ B then 1 else 0) :=
  step_gen M f μ0 0 h B μ0 (by simp [mdpStateKernel])

lemma step_succ (M : FiniteMDP S A) (f : Fin S → Fin A) (μ0 : MDPStateDistribution S) (n : ℕ)
    (h : MDPTrajectory S A (n+1)) (B : Set (Fin S × Fin A)) :
    mdpStepKernel M μ0 (mdpMemorylessDetPolicy f) (n+1) h B =
      ∑ s', (M.P (h (Fin.last n)).1 (h (Fin.last n)).2 s' : ℝ≥0∞) *
        (if (s', f s') ∈ B then 1 else 0) :=
  step_gen M f μ0 (n+1) h B (M.transitionDist (h (Fin.last n)).1 (h (Fin.last n)).2) (by
    rw [mdpStateKernel, Kernel.comap_apply]; rfl)


lemma lintegral_ok {m : ℕ} (tgt : Fin S) (μ : Measure (MDPTrajectory S A (m+1)))
    (g : Fin S × Fin A → ℝ≥0∞) :
    ∫⁻ h, (if (∀ t, (h t).1 ≠ tgt) then g (h (Fin.last m)) else 0) ∂μ =
      ∑ y, g y * μ {h | (∀ t, (h t).1 ≠ tgt) ∧ h (Fin.last m) = y} := by
  have : ∀ h : MDPTrajectory S A (m+1), (if (∀ t, (h t).1 ≠ tgt) then g (h (Fin.last m)) else 0) =
      ∑ y, Set.indicator {h : MDPTrajectory S A (m+1) | (∀ t, (h t).1 ≠ tgt) ∧ h (Fin.last m) = y}
        (fun _ => g y) h := by
    intro h
    by_cases hok : ∀ t, (h t).1 ≠ tgt
    · rw [if_pos hok, Finset.sum_eq_single (h (Fin.last m))]
      · simp [Set.indicator, hok]
      · intro y _ hy; simp [Set.indicator, hok, Ne.symm hy]
      · simp
    · rw [if_neg hok]; simp [Set.indicator, hok]
  simp_rw [this]
  rw [lintegral_finset_sum]
  · refine Finset.sum_congr rfl fun y _ => ?_
    rw [lintegral_indicator_const (meas_all _)]
  · intro y _; exact measurable_const.indicator (meas_all _)


/-- forward mass of avoiding `tgt` and ending in `x` -/
noncomputable def V (M : FiniteMDP S A) (f : Fin S → Fin A) (tgt src : Fin S) (n : ℕ)
    (x : Fin S × Fin A) : ℝ≥0∞ :=
  mdpMeasure M (mdpStateDirac src) (mdpMemorylessDetPolicy f) (n+1)
    {h | (∀ t, (h t).1 ≠ tgt) ∧ h (Fin.last n) = x}

lemma ok_snoc {n : ℕ} (tgt : Fin S) (h : MDPTrajectory S A (n+1)) (p : Fin S × Fin A) :
    (∀ t, ((Fin.snoc (α := fun _ => Fin S × Fin A) h p : MDPTrajectory S A (n+2)) t).1 ≠ tgt) ↔
      (∀ t, (h t).1 ≠ tgt) ∧ p.1 ≠ tgt := by
  rw [Fin.forall_fin_succ' (P := fun t => ((Fin.snoc (α := fun _ => Fin S × Fin A) h p : MDPTrajectory S A (n+2)) t).1 ≠ tgt)]
  simp

lemma V_succ (M : FiniteMDP S A) (f : Fin S → Fin A) (tgt src : Fin S) (n : ℕ)
    (x : Fin S × Fin A) :
    V M f tgt src (n+1) x =
      if x.1 ≠ tgt ∧ x.2 = f x.1 then ∑ y, V M f tgt src n y * (M.P y.1 y.2 x.1 : ℝ≥0∞) else 0 := by
  unfold V
  rw [mu_succ_apply]
  have key : ∀ h : MDPTrajectory S A (n+1),
      mdpStepKernel M (mdpStateDirac src) (mdpMemorylessDetPolicy f) (n+1) h
        {p | Fin.snoc (α := fun _ => Fin S × Fin A) h p ∈
          {h' : MDPTrajectory S A (n+2) | (∀ t, (h' t).1 ≠ tgt) ∧ h' (Fin.last (n+1)) = x}} =
      if x.1 ≠ tgt ∧ x.2 = f x.1 then
        (if (∀ t, (h t).1 ≠ tgt) then (M.P (h (Fin.last n)).1 (h (Fin.last n)).2 x.1 : ℝ≥0∞) else 0)
      else 0 := by
    intro h
    rw [step_succ]
    simp only [Set.mem_setOf_eq, ok_snoc, Fin.snoc_last]
    by_cases h1 : x.1 ≠ tgt ∧ x.2 = f x.1
    · rw [if_pos h1]
      by_cases hok : ∀ t, (h t).1 ≠ tgt
      · rw [if_pos hok, Finset.sum_eq_single x.1]
        · simp [hok, h1.1, ← h1.2]
        · intro s' _ hs'
          have : ¬ ((s', f s') = x) := fun hh => hs' (by rw [← hh])
          simp [hok, this]
        · simp
      · simp [hok]
    · rw [if_neg h1]
      simp only [Finset.sum_eq_zero_iff, Finset.mem_univ, forall_true_left]
      intro s'
      by_cases hs : (s', f s') = x
      · subst hs; simp at h1; simp [h1]
      · simp [hs]
  simp_rw [key]
  split_ifs with hx
  · have := lintegral_ok (m := n) tgt (mdpMeasure M (mdpStateDirac src) (mdpMemorylessDetPolicy f) (n+1))
      (fun y => (M.P y.1 y.2 x.1 : ℝ≥0∞))
    rw [this]
    exact Finset.sum_congr rfl fun y _ => mul_comm _ _
  · simp

lemma V_zero (M : FiniteMDP S A) (f : Fin S → Fin A) (tgt src : Fin S) (x : Fin S × Fin A) :
    V M f tgt src 0 x = if x.1 = src ∧ x.1 ≠ tgt ∧ x.2 = f x.1 then 1 else 0 := by
  unfold V
  rw [mu_succ_apply, mdpMeasure, lintegral_dirac]
  rw [step_zero]
  have hok : ∀ (h : MDPTrajectory S A 0) (p : Fin S × Fin A),
      (∀ t, ((Fin.snoc (α := fun _ => Fin S × Fin A) h p : MDPTrajectory S A (0+1)) t).1 ≠ tgt) ↔
        p.1 ≠ tgt := by
    intro h p
    rw [Fin.forall_fin_succ' (P := fun t => ((Fin.snoc (α := fun _ => Fin S × Fin A) h p : MDPTrajectory S A (0+1)) t).1 ≠ tgt)]
    simp only [Fin.snoc_last, IsEmpty.forall_iff, true_and]
  simp only [Set.mem_setOf_eq, hok, Fin.snoc_last, mdpStateDirac]
  by_cases h1 : x.1 = src ∧ x.1 ≠ tgt ∧ x.2 = f x.1
  · rw [if_pos h1, Finset.sum_eq_single x.1]
    · obtain ⟨e1, e2, e3⟩ := h1
      have e : (src, f src) = x := Prod.ext e1.symm (by rw [e3, e1])
      have e2' : src ≠ tgt := e1 ▸ e2
      simp [e1, e2', e]
    · intro s' _ hs'
      have : ¬ ((s', f s') = x) := fun hh => hs' (by rw [← hh])
      simp [this]
    · simp
  · rw [if_neg h1]
    refine Finset.sum_eq_zero fun s' _ => ?_
    by_cases hs : (s', f s') = x
    · subst hs
      simp at h1
      by_cases hs2 : s' = src
      · simp [hs2] at h1 ⊢; simp [h1]
      · simp [hs2]
    · simp [hs]

lemma V_off (M : FiniteMDP S A) (f : Fin S → Fin A) (tgt src : Fin S) (n : ℕ) (s : Fin S)
    (a : Fin A) (ha : a ≠ f s) : V M f tgt src n (s, a) = 0 := by
  cases n with
  | zero => rw [V_zero]; simp [ha]
  | succ n => rw [V_succ]; simp [ha]

/-- the sub-stochastic matrix of the policy `f`, killed at `tgt` -/
noncomputable def Bm (M : FiniteMDP S A) (f : Fin S → Fin A) (tgt : Fin S) :
    Matrix (Fin S) (Fin S) ℝ≥0∞ :=
  fun s s' => if s' ≠ tgt then (M.P s (f s) s' : ℝ≥0∞) else 0

lemma V_pow (M : FiniteMDP S A) (f : Fin S → Fin A) (tgt src : Fin S) (hs : src ≠ tgt) (n : ℕ)
    (s : Fin S) : V M f tgt src n (s, f s) = (Bm M f tgt ^ n) src s := by
  induction n generalizing s with
  | zero =>
    rw [V_zero, pow_zero, Matrix.one_apply]
    by_cases h : s = src
    · simp [h, hs]
    · simp [h, Ne.symm h]
  | succ n ih =>
    rw [V_succ, pow_succ, Matrix.mul_apply]
    by_cases ht : s = tgt
    · simp [ht, Bm]
    · simp only [ne_eq, ht, not_false_eq_true, true_and, if_true]
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.sum_eq_single (f y)]
      · simp [ih, Bm, ht]
      · intro a _ ha; rw [V_off _ _ _ _ _ _ _ ha]; simp
      · simp
    
lemma Qm_eq (M : FiniteMDP S A) (f : Fin S → Fin A) (tgt src : Fin S) (hs : src ≠ tgt) (n : ℕ) :
    mdpMeasure M (mdpStateDirac src) (mdpMemorylessDetPolicy f) (n+1) {h | ∀ t, (h t).1 ≠ tgt} =
      ∑ s, (Bm M f tgt ^ n) src s := by
  have h1 := lintegral_ok (m := n) tgt (mdpMeasure M (mdpStateDirac src) (mdpMemorylessDetPolicy f) (n+1))
      (fun _ => (1 : ℝ≥0∞))
  have h2 : ∫⁻ h, (if (∀ t, (h t).1 ≠ tgt) then (fun _ : Fin S × Fin A => (1 : ℝ≥0∞)) (h (Fin.last n)) else 0)
      ∂(mdpMeasure M (mdpStateDirac src) (mdpMemorylessDetPolicy f) (n+1)) =
      mdpMeasure M (mdpStateDirac src) (mdpMemorylessDetPolicy f) (n+1) {h | ∀ t, (h t).1 ≠ tgt} := by
    have : ∀ h : MDPTrajectory S A (n+1), (if (∀ t, (h t).1 ≠ tgt) then (fun _ : Fin S × Fin A => (1 : ℝ≥0∞)) (h (Fin.last n)) else 0) =
        Set.indicator {h : MDPTrajectory S A (n+1) | ∀ t, (h t).1 ≠ tgt} (fun _ => (1 : ℝ≥0∞)) h := by
      intro h; simp [Set.indicator]
    simp_rw [this]
    rw [lintegral_indicator_const (meas_all _)]; simp
  rw [← h2, h1]
  simp only [one_mul]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_eq_single (f s)]
  · exact V_pow M f tgt src hs n s
  · intro a _ ha; exact V_off _ _ _ _ _ _ _ ha
  · simp

noncomputable def qq (M : FiniteMDP S A) (f : Fin S → Fin A) (tgt : Fin S) (n : ℕ) (s : Fin S) :
    ℝ≥0∞ := ∑ t, (Bm M f tgt ^ n) s t

lemma qq_zero (M : FiniteMDP S A) (f : Fin S → Fin A) (tgt s : Fin S) : qq M f tgt 0 s = 1 := by
  simp [qq, Matrix.one_apply]

lemma qq_succ (M : FiniteMDP S A) (f : Fin S → Fin A) (tgt s : Fin S) (n : ℕ) :
    qq M f tgt (n+1) s = ∑ k, Bm M f tgt s k * qq M f tgt n k := by
  unfold qq
  rw [pow_succ']
  simp only [Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma travel_eq (M : FiniteMDP S A) (f : Fin S → Fin A) (src tgt : Fin S) (hs : src ≠ tgt) :
    mdpTravelTime M f src tgt = ∑' k, qq M f tgt k src := by
  unfold mdpTravelTime
  refine tsum_congr fun k => ?_
  rw [Qm_eq M f tgt src hs k]; rfl

end QQE
end VVQ

open BanditAlgorithm NNReal ENNReal in
theorem solution {S A' : ℕ} (M' : FiniteMDP S A') (g : Fin S → Fin A')
    (tgt : Fin S) (E : Fin S → ℝ≥0∞) (δ : ℝ≥0) (hδ : δ < 1)
    (hsuper : ∀ s, s ≠ tgt →
      1 + ∑ s' ∈ Finset.univ.erase tgt, (M'.P s (g s) s' : ℝ≥0∞) * E s' ≤ E s + δ) :
    ∀ s, s ≠ tgt → ((1 - δ : ℝ≥0) : ℝ≥0∞) * mdpTravelTime M' g s tgt ≤ E s := by
  classical
  set c : ℝ≥0∞ := ((1 - δ : ℝ≥0) : ℝ≥0∞) with hc
  have hcδ : c + δ = 1 := by
    rw [hc, ← ENNReal.coe_add]
    have : (1 - δ) + δ = 1 := tsub_add_cancel_of_le hδ.le
    rw [this]; simp
  have hδtop : (δ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hsum : ∀ n s, ∑ k ∈ Finset.range (n+1), QQE.qq M' g tgt k s =
      1 + ∑ s' ∈ Finset.univ.erase tgt, (M'.P s (g s) s' : ℝ≥0∞) * ∑ k ∈ Finset.range n, QQE.qq M' g tgt k s' := by
    intro n s
    rw [Finset.sum_range_succ', QQE.qq_zero, add_comm]
    congr 1
    simp_rw [QQE.qq_succ]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ tgt)]
    have h0 : QQE.Bm M' g tgt s tgt * ∑ k ∈ Finset.range n, QQE.qq M' g tgt k tgt = 0 := by simp [QQE.Bm]
    rw [h0, zero_add]
    refine Finset.sum_congr rfl fun s' hs' => ?_
    have hs'' : s' ≠ tgt := Finset.ne_of_mem_erase hs'
    simp [QQE.Bm, hs'']
  have hind : ∀ n, ∀ s, s ≠ tgt → c * ∑ k ∈ Finset.range n, QQE.qq M' g tgt k s ≤ E s := by
    intro n
    induction n with
    | zero => intro s _; simp
    | succ n ih =>
      intro s hs
      rw [hsum, mul_add, mul_one, Finset.mul_sum]
      have h1 : ∑ s' ∈ Finset.univ.erase tgt, c * ((M'.P s (g s) s' : ℝ≥0∞) * ∑ k ∈ Finset.range n, QQE.qq M' g tgt k s')
          ≤ ∑ s' ∈ Finset.univ.erase tgt, (M'.P s (g s) s' : ℝ≥0∞) * E s' := by
        refine Finset.sum_le_sum fun s' hs' => ?_
        have hs'' : s' ≠ tgt := Finset.ne_of_mem_erase hs'
        calc c * ((M'.P s (g s) s' : ℝ≥0∞) * ∑ k ∈ Finset.range n, QQE.qq M' g tgt k s')
            = (M'.P s (g s) s' : ℝ≥0∞) * (c * ∑ k ∈ Finset.range n, QQE.qq M' g tgt k s') := by ring
          _ ≤ (M'.P s (g s) s' : ℝ≥0∞) * E s' := by gcongr; exact ih s' hs''
      have h2 : c + ∑ s' ∈ Finset.univ.erase tgt, (M'.P s (g s) s' : ℝ≥0∞) * E s' ≤ E s := by
        have := hsuper s hs
        rw [← hcδ, add_assoc] at this
        rw [add_comm (E s) δ] at this
        rw [add_comm] at this
        have h3 : (c + ∑ s' ∈ Finset.univ.erase tgt, (M'.P s (g s) s' : ℝ≥0∞) * E s') + δ ≤ E s + δ := by
          calc _ = (c + δ) + ∑ s' ∈ Finset.univ.erase tgt, (M'.P s (g s) s' : ℝ≥0∞) * E s' := by ring
            _ = 1 + ∑ s' ∈ Finset.univ.erase tgt, (M'.P s (g s) s' : ℝ≥0∞) * E s' := by rw [hcδ]
            _ ≤ E s + δ := hsuper s hs
        exact (ENNReal.add_le_add_iff_right hδtop).1 h3
      calc c + ∑ s' ∈ Finset.univ.erase tgt, c * ((M'.P s (g s) s' : ℝ≥0∞) * ∑ k ∈ Finset.range n, QQE.qq M' g tgt k s')
          ≤ c + ∑ s' ∈ Finset.univ.erase tgt, (M'.P s (g s) s' : ℝ≥0∞) * E s' := by gcongr
        _ ≤ E s := h2
  intro s hs
  rw [QQE.travel_eq M' g s tgt hs, ENNReal.tsum_eq_iSup_nat, ENNReal.mul_iSup]
  exact iSup_le fun n => hind n s hs
