-- Prove2me | solution 1 for RiskSensMDP.Discounted.optimal_history_policy
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T02:14:22.163104+00:00
-- url     : https://prove2.me/submissions/028257d9-1c6e-495e-8490-5627ac91d77d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RiskSensMDP_Discounted_Model
import Theorems.Thm_RiskSensMDP_Discounted_value_iteration
import Theorems.Thm_RiskSensMDP_Discounted_operator_preserves_class

open MeasureTheory ProbabilityTheory Filter
open RiskSensMDP.Discounted

namespace RSMDP2Aux

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

lemma dHC_nonneg (M : Model E A) (hB : HasBounds M) (l : List (E × A))
    (hl : ∀ p ∈ l, p ∈ M.P.D) : 0 ≤ discountedHistoryCost M l := by
  induction l with
  | nil => simp [discountedHistoryCost]
  | cons p ps ih =>
    simp only [discountedHistoryCost]
    have h1 := (hB.2.2.2.1 p (hl p (by simp))).1
    have h2 := ih (fun q hq => hl q (by simp [hq]))
    have h3 : 0 ≤ M.β * discountedHistoryCost M ps := mul_nonneg hB.2.2.2.2.1.le h2
    linarith [hB.2.1]

lemma dHC_append (M : Model E A) (l : List (E × A)) (p : E × A) :
    discountedHistoryCost M (l ++ [p]) =
      discountedHistoryCost M l + M.β ^ l.length * M.c p := by
  induction l with
  | nil => simp [discountedHistoryCost]
  | cons q l ih =>
    simp only [List.cons_append, discountedHistoryCost, ih, List.length_cons, pow_succ]
    ring

noncomputable def cOpt (M : Model E A) : Option (E × A) → ℝ
  | none => 0
  | some p => M.c p

lemma cOpt_meas (M : Model E A) (hc : Measurable M.c) : Measurable (cOpt M) := by
  intro S hS
  have h1 : MeasurableSet ({none} : Set (Option (E × A))) :=
    MeasurableSpace.measurableSet_generateFrom (Or.inl rfl)
  have h2 : MeasurableSet (Option.some '' (M.c ⁻¹' S) : Set (Option (E × A))) :=
    MeasurableSpace.measurableSet_generateFrom (Or.inr ⟨_, hc hS, rfl⟩)
  by_cases h0 : (0:ℝ) ∈ S
  · have : cOpt M ⁻¹' S = {none} ∪ Option.some '' (M.c ⁻¹' S) := by
      ext o; cases o <;> simp [cOpt, h0]
    rw [this]; exact h1.union h2
  · have : cOpt M ⁻¹' S = Option.some '' (M.c ⁻¹' S) := by
      ext o; cases o <;> simp [cOpt, h0]
    rw [this]; exact h2

lemma dHC_eq_sum (M : Model E A) (l : List (E × A)) :
    discountedHistoryCost M l =
      ∑ i ∈ Finset.range l.length, M.β ^ i * cOpt M (l[i]?) := by
  induction l with
  | nil => simp [discountedHistoryCost]
  | cons p l ih =>
    rw [List.length_cons, Finset.sum_range_succ', discountedHistoryCost, ih,
      Finset.mul_sum]
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, pow_zero, one_mul,
      cOpt, pow_succ]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring

lemma get_meas (n : ℕ) : Measurable (fun l : List (E × A) => l[n]?) :=
  (measurable_pi_apply n).comp (fun s hs => ⟨s, hs, rfl⟩)

lemma dHC_meas (M : Model E A) (hc : Measurable M.c) (n : ℕ) :
    Measurable (fun h : {h : History E A // ValidHistory M.P n h} =>
      discountedHistoryCost M h.1.1) := by
  have : (fun h : {h : History E A // ValidHistory M.P n h} =>
      discountedHistoryCost M h.1.1) =
      fun h => ∑ i ∈ Finset.range n, M.β ^ i * cOpt M (h.1.1[i]?) := by
    funext h; rw [dHC_eq_sum, h.2.1]
  rw [this]
  exact Finset.measurable_sum _ (fun i _ => measurable_const.mul
    ((cOpt_meas M hc).comp ((get_meas i).comp (measurable_fst.comp measurable_subtype_coe))))

/-- The history policy of Theorem 3.6(c). -/
noncomputable def optPolicy (M : Model E A) (hB : HasBounds M) (N : ℕ)
    (fs : ℕ → DecisionRule M) : Policy M.P where
  g n h := (fs (N - n)).f (h.2, (discountedHistoryCost M h.1, M.β ^ n))
  measurable_g n := (fs (N - n)).measurable_f.comp
    ((measurable_snd.comp measurable_subtype_coe).prodMk
      ((dHC_meas M hB.1 n).prodMk measurable_const))
  admissible_g n h hv := (fs (N - n)).admissible_f (h.2, (discountedHistoryCost M h.1, M.β ^ n))
    ⟨dHC_nonneg M hB h.1 hv.2, pow_pos hB.2.2.2.2.1 n,
      pow_le_one₀ hB.2.2.2.2.1.le hB.2.2.2.2.2.le⟩

lemma valid_append (P : ControlledMDP E A) (k : ℕ) (h : History E A)
    (hv : ValidHistory P k h) (a : A) (ha : (h.2, a) ∈ P.D) (x' : E) :
    ValidHistory P (k + 1) (h.1 ++ [(h.2, a)], x') := by
  refine ⟨by simp [hv.1], ?_⟩
  intro q hq
  simp only [List.mem_append, List.mem_singleton] at hq
  rcases hq with hq | rfl
  · exact hv.2 q hq
  · exact ha

lemma expectedFrom_bound (M : Model E A) (hB : HasBounds M) (σ : Policy M.P) (T B : ℝ)
    (hUB : ∀ t ∈ Set.Icc (0:ℝ) T, |M.U t| ≤ B) :
    ∀ (n k : ℕ) (h : History E A) (y z : ℝ), ValidHistory M.P k h → 0 ≤ y → 0 < z → z ≤ 1 →
      y + z * n * M.upperCost ≤ T → |expectedFrom M σ.g k h n y z| ≤ B := by
  intro n
  induction n with
  | zero =>
    intro k h y z hv hy hz hz1 hT
    simp only [expectedFrom]
    exact hUB y ⟨hy, by simpa using hT⟩
  | succ n ih =>
    intro k h y z hv hy hz hz1 hT
    rw [expectedFrom]
    have hD := σ.admissible_g k h hv
    have hc := hB.2.2.2.1 _ hD
    have hlow := hB.2.1
    have hup : 0 < M.upperCost := lt_trans hB.2.1 hB.2.2.1
    have hβ0 := hB.2.2.2.2.1
    have hβ1 := hB.2.2.2.2.2
    have := M.P.markov_Q
    have hbd := norm_integral_le_of_norm_le_const (μ := M.P.Q (h.2, σ.g k h)) (C := B)
      (f := fun x' => expectedFrom M σ.g (k + 1) (h.1 ++ [(h.2, σ.g k h)], x') n
        (y + z * M.c (h.2, σ.g k h)) (z * M.β))
      (Filter.Eventually.of_forall fun x' => ?_)
    · simpa [Real.norm_eq_abs, probReal_univ] using hbd
    rw [Real.norm_eq_abs]
    refine ih (k + 1) _ _ _ (valid_append M.P k h hv _ hD x') ?_ (mul_pos hz hβ0) ?_ ?_
    · have : 0 ≤ z * M.c (h.2, σ.g k h) := mul_nonneg hz.le (by linarith [hc.1])
      linarith
    · nlinarith
    · have e1 : z * M.c (h.2, σ.g k h) ≤ z * M.upperCost :=
        mul_le_mul_of_nonneg_left hc.2 hz.le
      have e2 : z * M.β * (n : ℝ) * M.upperCost ≤ z * (n : ℝ) * M.upperCost := by
        have h0 : 0 ≤ z * (n : ℝ) * M.upperCost := by positivity
        nlinarith
      push_cast at hT
      nlinarith

end RSMDP2Aux

open RSMDP2Aux in
theorem solution {E A : Type*}
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace.MetrizableSpace E] [SecondCountableTopology E]
    [StandardBorelSpace E]
    [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [StandardBorelSpace A]
    (M : Model E A) (hBounds : HasBounds M) (hCC : HasCC M)
    (N : ℕ) :
    (∀ k ∈ Finset.Icc 1 N,
      ∃ f : DecisionRule M,
        IsMinimizer M (fun s => value M (k - 1) s.1 s.2.1 s.2.2) f) ∧
    (∀ fs : ℕ → DecisionRule M,
      (∀ k ∈ Finset.Icc 1 N,
        IsMinimizer M (fun s => value M (k - 1) s.1 s.2.1 s.2.2) (fs k)) →
      ∃ σ : Policy M.P,
        (∀ n < N, ∀ h : History E A, ValidHistory M.P n h →
          σ.g n h =
            (fs (N - n)).f
              (h.2, (discountedHistoryCost M h.1, M.β ^ n))) ∧
        (∀ x : E, policyValue M σ N x 0 1 = objective M N x)) := by
  obtain ⟨hVI0, hVI2, hVI3⟩ := value_iteration M hBounds hCC N
  have hβ0 := hBounds.2.2.2.2.1
  have hβ1 := hBounds.2.2.2.2.2
  refine ⟨?_, ?_⟩
  · -- existence of minimizers
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    have hIC := hVI2 (k - 1) (by omega)
    refine (operator_preserves_class M hBounds hCC _ hIC ?_).2
    intro s hs a ha
    have hc := hBounds.2.2.2.1 _ ha
    set y' := s.2.1 + s.2.2 * M.c (s.1, a) with hy'
    set z' := s.2.2 * M.β with hz'
    have hy0 : 0 ≤ y' := by
      have : 0 ≤ s.2.2 * M.c (s.1, a) := mul_nonneg hs.2.1.le (by linarith [hc.1, hBounds.2.1])
      linarith [hs.1]
    have hz0 : 0 < z' := mul_pos hs.2.1 hβ0
    have hz1 : z' ≤ 1 := by nlinarith [hs.2.2]
    -- measurability of the slice
    have hmeas : Measurable (fun x' => value M (k - 1) x' y' z') := by
      have hl := hIC.1.comp (g := fun x' : E => ((x', (y', z')) : ExtendedState E))
        (t := Set.univ) (by fun_prop) (fun x' _ => ⟨hy0, hz0, hz1⟩)
      exact (lowerSemicontinuousOn_univ_iff.mp hl).measurable
    -- boundedness of the slice
    set T := y' + z' * ((k - 1 : ℕ) : ℝ) * M.upperCost with hT
    have hT0 : 0 ≤ T := by
      have : 0 ≤ z' * ((k - 1 : ℕ) : ℝ) * M.upperCost := by
        have := lt_trans hBounds.2.1 hBounds.2.2.1
        positivity
      linarith
    obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_bound_of_continuousOn
      (hCC.1.mono Set.Icc_subset_Ici_self)
    have hUB : ∀ t ∈ Set.Icc (0:ℝ) T, |M.U t| ≤ B := fun t ht => by
      simpa [Real.norm_eq_abs] using hB t ht
    have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hUB 0 ⟨le_rfl, hT0⟩)
    have hpol : ∀ (τ : Policy M.P) (x' : E), |policyValue M τ (k - 1) x' y' z'| ≤ B :=
      fun τ x' => expectedFrom_bound M hBounds τ T B hUB (k - 1) 0 ([], x') y' z'
        ⟨rfl, by simp⟩ hy0 hz0 hz1 le_rfl
    have hbd : ∀ x', |value M (k - 1) x' y' z'| ≤ B := by
      intro x'
      rw [abs_le]
      constructor
      · have h1 := hIC.2.2.2 (x', (y', z')) ⟨hy0, hz0, hz1⟩
        have h2 := hUB y' ⟨hy0, by
          have : 0 ≤ z' * ((k - 1 : ℕ) : ℝ) * M.upperCost := by
            have := lt_trans hBounds.2.1 hBounds.2.2.1
            positivity
          linarith⟩
        rw [abs_le] at h2
        simp only at h1
        linarith [h2.1]
      · rcases isEmpty_or_nonempty (Policy M.P) with hE | hne
        · simp only [value, Real.iInf_of_isEmpty]; exact hB0
        · obtain ⟨τ⟩ := hne
          have hbdd : BddBelow (Set.range fun σ : Policy M.P => policyValue M σ (k - 1) x' y' z') :=
            ⟨-B, by rintro _ ⟨σ, rfl⟩; exact (abs_le.mp (hpol σ x')).1⟩
          exact le_trans (ciInf_le hbdd τ) (abs_le.mp (hpol τ x')).2
    have := M.P.markov_Q
    exact Integrable.of_bound hmeas.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun x' => by simpa [Real.norm_eq_abs] using hbd x')
  · -- optimality of the history policy
    intro fs hfs
    refine ⟨optPolicy M hBounds N fs, fun n _ h _ => rfl, ?_⟩
    have claim : ∀ n ≤ N, ∀ h : History E A, ValidHistory M.P (N - n) h →
        expectedFrom M (optPolicy M hBounds N fs).g (N - n) h n
          (discountedHistoryCost M h.1) (M.β ^ (N - n)) =
        value M n h.2 (discountedHistoryCost M h.1) (M.β ^ (N - n)) := by
      intro n
      induction n with
      | zero =>
        intro _ h hv
        simp only [expectedFrom]
        exact (hVI0 (h.2, (discountedHistoryCost M h.1, M.β ^ (N - 0)))
          ⟨dHC_nonneg M hBounds h.1 hv.2, pow_pos hβ0 _, pow_le_one₀ hβ0.le hβ1.le⟩).symm
      | succ n ih =>
        intro hn h hv
        set σ := optPolicy M hBounds N fs with hσ
        set k := N - (n + 1) with hk
        have hD := σ.admissible_g k h hv
        have e1 : k + 1 = N - n := by omega
        have key : ∀ x', expectedFrom M σ.g (k + 1) (h.1 ++ [(h.2, σ.g k h)], x') n
            (discountedHistoryCost M h.1 + M.β ^ k * M.c (h.2, σ.g k h)) (M.β ^ k * M.β) =
            value M n x' (discountedHistoryCost M h.1 + M.β ^ k * M.c (h.2, σ.g k h))
              (M.β ^ k * M.β) := by
          intro x'
          have := ih (by omega) (h.1 ++ [(h.2, σ.g k h)], x')
            (e1 ▸ valid_append M.P k h hv _ hD x')
          simp only [dHC_append, hv.1] at this
          rw [← pow_succ, e1]
          exact this
        rw [expectedFrom, integral_congr_ae (ae_of_all _ key)]
        have hs : ((h.2, (discountedHistoryCost M h.1, M.β ^ k)) : ExtendedState E) ∈
            extendedDomain E :=
          ⟨dHC_nonneg M hBounds h.1 hv.2, pow_pos hβ0 _, pow_le_one₀ hβ0.le hβ1.le⟩
        have hmem : n + 1 ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, hn⟩
        have hm := hfs (n + 1) hmem _ hs
        have hv3 := hVI3 (n + 1) hmem _ hs
        simp only [Nat.add_sub_cancel] at hm hv3
        rw [hv3, ← hm]
        have hNk : N - k = n + 1 := by omega
        simp only [decisionOperator, oneStep]
        show _ = ∫ x', value M n x' _ _ ∂(M.P.Q (h.2, (fs (n + 1)).f _))
        have hg : σ.g k h = (fs (n + 1)).f (h.2, (discountedHistoryCost M h.1, M.β ^ k)) := by
          show (fs (N - k)).f _ = _
          rw [hNk]
        rw [hg]
    intro x
    have := claim N le_rfl ([], x) ⟨by simp, by simp⟩
    simpa [discountedHistoryCost, policyValue, objective] using this
