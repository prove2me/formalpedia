-- Prove2me | solution 1 for OnDemandCoord.priorityAlloc_noWaste
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:52:01.657228+00:00
-- url     : https://prove2.me/submissions/e48cfce6-893a-47ee-b3cc-fde2dcadfc26

import Mathlib
import Definitions.Def_OnDemandCoord_Coordinates

set_option autoImplicit false

open MeasureTheory ProbabilityTheory OnDemandCoord
open scoped ENNReal

namespace OnDemandCoord.PriorityProof

theorem min_step_eq (r A B : ℝ) (hB : 0 ≤ B) :
    min r A + min B (max (r - A) 0) = min r (A + B) := by
  by_cases hrA : r ≤ A
  · have hmax : max (r - A) 0 = 0 := max_eq_right (by linarith)
    rw [min_eq_left hrA, hmax, min_eq_right hB, add_zero, min_eq_left (by linarith)]
  · push Not at hrA
    have hmax : max (r - A) 0 = r - A := max_eq_left (by linarith)
    rw [min_eq_right hrA.le, hmax]
    by_cases hBr : B ≤ r - A
    · rw [min_eq_left hBr, min_eq_right (by linarith)]
    · push Not at hBr
      rw [min_eq_right hBr.le, add_sub_cancel, min_eq_left (by linarith)]

theorem prefix_sum {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (r : ℝ)
    (hx : 0 ≤ x) (hr : 0 ≤ r) :
    ∀ j : ℕ, j ≤ n →
      ∑ l ∈ Finset.univ.filter (fun l : Fin n => (l : ℕ) < j), priorityAlloc σ x r (σ l) =
        min r (∑ l ∈ Finset.univ.filter (fun l : Fin n => (l : ℕ) < j), x (σ l))
  | 0, _ => by
    simp [min_eq_right hr]
  | j + 1, hjn => by
    let k : Fin n := ⟨j, hjn⟩
    have ih := prefix_sum σ x r hx hr j (by omega)
    have hfilt : Finset.univ.filter (fun l : Fin n => (l : ℕ) < j + 1) =
        insert k (Finset.univ.filter (fun l : Fin n => (l : ℕ) < j)) := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro hl
        by_cases heq : (l : ℕ) = j
        · exact Or.inl (Fin.ext heq)
        · exact Or.inr (by omega)
      · rintro (rfl | hl)
        · exact Nat.lt_succ_self j
        · omega
    have hnotmem : k ∉ Finset.univ.filter (fun l : Fin n => (l : ℕ) < j) := by
      simp [k]
    rw [hfilt, Finset.sum_insert hnotmem, Finset.sum_insert hnotmem, add_comm (priorityAlloc _ _ _ _),
      ih, add_comm (x (σ k))]
    have hpa : priorityAlloc σ x r (σ k) =
        min (x (σ k)) (max (r - ∑ l ∈ Finset.univ.filter (fun l : Fin n => (l : ℕ) < j), x (σ l)) 0) := by
      unfold priorityAlloc
      simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply]
      rfl
    rw [hpa]
    exact min_step_eq r _ (x (σ k)) (hx (σ k))

theorem measurable_extendSample {n T : ℕ} (k : ℕ) :
    Measurable (fun ξ : Fin T → Fin n → ℝ => extendSample ξ k) := by
  unfold extendSample
  split_ifs with hk
  · exact measurable_pi_apply (⟨k, hk⟩ : Fin T)
  · exact measurable_const

theorem measurable_cumAlloc {n : ℕ} (T : ℕ) {s : ℝ} (run : RunData n s) (β m : Fin n → ℝ) :
    ∀ t : ℕ, Measurable (fun ξ : Fin T → Fin n → ℝ => run.cumAlloc β m (extendSample ξ) t)
  | 0 => measurable_const
  | 1 => run.measurable_a₁.comp (measurable_extendSample 0)
  | t + 2 => by
    have ih := measurable_cumAlloc T run β m (t + 1)
    let debt : (Fin T → Fin n → ℝ) → (Fin n → ℝ) :=
      fun ξ i => ((t + 1 : ℕ) : ℝ) * (β i * m i) - run.cumAlloc β m (extendSample ξ) (t + 1) i
    have hdebt : Measurable debt := by
      refine measurable_pi_lambda _ fun i => ?_
      exact measurable_const.sub ((measurable_pi_apply i).comp ih)
    let stepFn : (Fin T → Fin n → ℝ) → (Fin n → ℝ) :=
      fun ξ => priorityAlloc (run.pick (debt ξ)) (extendSample ξ (t + 1)) s
    have hstep_eq : stepFn = fun ξ =>
        ∑ σ : Equiv.Perm (Fin n),
          (debt ⁻¹' (run.pick ⁻¹' {σ})).indicator
            (fun ξ' => priorityAlloc σ (extendSample ξ' (t + 1)) s) ξ := by
      ext ξ i
      rw [Finset.sum_apply, Finset.sum_eq_single (run.pick (debt ξ))]
      · simp [Set.indicator_of_mem]; rfl
      · intro σ _ hne
        have hnot : ξ ∉ debt ⁻¹' (run.pick ⁻¹' {σ}) := by
          simp [Set.mem_preimage, hne.symm]
        simp [Set.indicator_of_notMem hnot]
      · intro habs; exact absurd (Finset.mem_univ _) habs
    have hstep_meas : Measurable stepFn := by
      rw [hstep_eq]
      refine Finset.measurable_sum Finset.univ fun σ _ => ?_
      have hFσ : Measurable (fun ξ' : Fin T → Fin n → ℝ =>
          priorityAlloc σ (extendSample ξ' (t + 1)) s) :=
        (measurable_priorityAlloc σ).comp ((measurable_extendSample (t + 1)).prodMk measurable_const)
      exact hFσ.indicator ((run.measurableSet_pick σ).preimage hdebt)
    unfold RunData.cumAlloc
    exact ih.add hstep_meas

theorem listWeight_nonneg_and_sum_one {n : ℕ} {s : ℝ} (run : RunData n s) (β m : Fin n → ℝ)
    (ν : Measure (Fin n → ℝ)) [IsProbabilityMeasure ν] {T : ℕ} (hT : 2 ≤ T) :
    (∀ σ : Equiv.Perm (Fin n), 0 ≤ run.listWeight β m ν T σ) ∧
      ∑ σ : Equiv.Perm (Fin n), run.listWeight β m ν T σ = 1 := by
  have hT1_pos : (0 : ℝ) < (T : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (T : ℝ) := Nat.ofNat_le_cast.mpr hT
    linarith
  constructor
  · intro σ
    unfold RunData.listWeight
    exact mul_nonneg (inv_nonneg.mpr hT1_pos.le) (Finset.sum_nonneg fun _ _ => measureReal_nonneg)
  · unfold RunData.listWeight
    rw [← Finset.mul_sum, Finset.sum_comm]
    have ht_one : ∀ t ∈ Finset.Ico 1 T,
        ∑ σ : Equiv.Perm (Fin n),
          (sampleLaw ν T).real {ξ | run.priorityList β m (extendSample ξ) t = σ} = 1 := by
      intro t _
      unfold sampleLaw
      let debt : (Fin T → Fin n → ℝ) → (Fin n → ℝ) :=
        fun ξ i => (t : ℝ) * (β i * m i) - run.cumAlloc β m (extendSample ξ) t i
      have hdebt : Measurable debt := by
        refine measurable_pi_lambda _ fun i => ?_
        exact measurable_const.sub ((measurable_pi_apply i).comp (measurable_cumAlloc T run β m t))
      let E : Equiv.Perm (Fin n) → Set (Fin T → Fin n → ℝ) :=
        fun σ => debt ⁻¹' (run.pick ⁻¹' {σ})
      have hE_meas : ∀ σ, MeasurableSet (E σ) :=
        fun σ => (run.measurableSet_pick σ).preimage hdebt
      have hE_disj :
          ((Finset.univ : Finset (Equiv.Perm (Fin n))) : Set (Equiv.Perm (Fin n))).PairwiseDisjoint E := by
        intro σ₁ _ σ₂ _ hne
        change Disjoint (E σ₁) (E σ₂)
        rw [Set.disjoint_left]
        intro ξ h₁ h₂
        apply hne
        have e1 : run.pick (debt ξ) = σ₁ := h₁
        have e2 : run.pick (debt ξ) = σ₂ := h₂
        exact e1.symm.trans e2
      have hbiU : (⋃ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))), E σ) = Set.univ := by
        ext ξ
        simp [E]
      have hsum_real : ∑ σ : Equiv.Perm (Fin n),
            (Measure.pi fun _ : Fin T => ν).real (E σ) =
          (Measure.pi fun _ : Fin T => ν).real
            (⋃ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))), E σ) :=
        (measureReal_biUnion_finset hE_disj fun σ _ => hE_meas σ).symm
      change ∑ σ : Equiv.Perm (Fin n), (Measure.pi fun _ : Fin T => ν).real (E σ) = 1
      rw [hsum_real, hbiU, probReal_univ]
    rw [Finset.sum_congr rfl ht_one]
    simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
    have hcast : ((T - 1 : ℕ) : ℝ) = (T : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [hcast, inv_mul_cancel₀ hT1_pos.ne']

end OnDemandCoord.PriorityProof

open OnDemandCoord.PriorityProof in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} (M : Model Ω P n)
    (Q : Fin n → ℝ) (s : ℝ) (β : Fin n → ℝ) (run : RunData n s) (T : ℕ) (hT : 2 ≤ T) :
    (∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (r : ℝ), 0 ≤ x → 0 ≤ r →
      IsFeasibleAlloc x r (priorityAlloc σ x r) ∧
      ∑ i, priorityAlloc σ x r i = min r (∑ i, x i) ∧
      ∀ j : ℕ, j ≤ n →
        ∑ l ∈ Finset.univ.filter (fun l : Fin n => (l : ℕ) < j), priorityAlloc σ x r (σ l) =
          min r (∑ l ∈ Finset.univ.filter (fun l : Fin n => (l : ℕ) < j), x (σ l))) ∧
    IsPolicy (M.tfrb Q s β run T) ∧ IsNoWaste (M.tfrb Q s β run T) := by
  have hdet : ∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (r : ℝ), 0 ≤ x → 0 ≤ r →
      IsFeasibleAlloc x r (priorityAlloc σ x r) ∧
      ∑ i, priorityAlloc σ x r i = min r (∑ i, x i) ∧
      ∀ j : ℕ, j ≤ n →
        ∑ l ∈ Finset.univ.filter (fun l : Fin n => (l : ℕ) < j), priorityAlloc σ x r (σ l) =
          min r (∑ l ∈ Finset.univ.filter (fun l : Fin n => (l : ℕ) < j), x (σ l)) := by
    intro σ x r hx hr
    have hpref := prefix_sum σ x r hx hr
    have huniv : Finset.univ.filter (fun l : Fin n => (l : ℕ) < n) = Finset.univ :=
      Finset.filter_true_of_mem fun l _ => l.isLt
    have htot : ∑ i, priorityAlloc σ x r i = min r (∑ i, x i) := by
      have hn := hpref n le_rfl
      rw [huniv] at hn
      rw [← Equiv.sum_comp σ (priorityAlloc σ x r), ← Equiv.sum_comp σ x]
      exact hn
    have hfeas : IsFeasibleAlloc x r (priorityAlloc σ x r) := by
      refine ⟨fun i => ⟨le_min (hx i) (le_max_right _ _), min_le_left _ _⟩, ?_⟩
      rw [htot]
      exact min_le_left _ _
    exact ⟨hfeas, htot, hpref⟩
  have : IsProbabilityMeasure P := M.isProb
  let ν : Measure (Fin n → ℝ) := P.map (M.vacVec Q)
  have : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (M.measurable_vacVec Q).aemeasurable
  obtain ⟨hw_nn, hw_sum⟩ := listWeight_nonneg_and_sum_one run β (M.mean Q) ν hT
  have hmarkov : IsMarkovKernel (M.tfrb Q s β run T) := by
    refine ⟨fun z => ⟨?_⟩⟩
    change (∑ σ : Equiv.Perm (Fin n),
      ENNReal.ofReal (run.listWeight β (M.mean Q) ν T σ) •
        Measure.dirac (priorityAlloc σ z.1 z.2)) Set.univ = 1
    simp only [Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
      (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg fun σ _ => hw_nn σ, hw_sum, ENNReal.ofReal_one]
  have hae_dirac_sum : ∀ (x : Fin n → ℝ) (r : ℝ) (PropFn : (Fin n → ℝ) → Prop),
      (∀ σ : Equiv.Perm (Fin n), PropFn (priorityAlloc σ x r)) →
      ∀ᵐ a ∂(M.tfrb Q s β run T) (x, r), PropFn a := by
    intro x r PropFn hall
    rw [ae_iff]
    change (∑ σ : Equiv.Perm (Fin n),
      ENNReal.ofReal (run.listWeight β (M.mean Q) ν T σ) •
        Measure.dirac (priorityAlloc σ x r)) {a | ¬ PropFn a} = 0
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro σ _
    have hsub : {a : Fin n → ℝ | ¬ PropFn a} ⊆ {priorityAlloc σ x r}ᶜ := by
      intro a ha hmem
      exact ha ((Set.mem_singleton_iff.mp hmem) ▸ hall σ)
    have hcompl0 : (Measure.dirac (priorityAlloc σ x r)) ({priorityAlloc σ x r}ᶜ) = 0 := by
      rw [Measure.dirac_apply' _ (MeasurableSet.singleton _).compl]
      simp
    rw [measure_mono_null hsub hcompl0, mul_zero]
  refine ⟨hdet, ⟨hmarkov, fun x r hx hr => ?_⟩, fun x r hx hr => ?_⟩
  · exact hae_dirac_sum x r _ fun σ => (hdet σ x r hx hr).1
  · exact hae_dirac_sum x r _ fun σ => (hdet σ x r hx hr).2.1
