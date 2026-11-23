-- Prove2me | solution 1 for OnDemandCoord.eq_15
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:55:06.083148+00:00
-- url     : https://prove2.me/submissions/4fd373ce-ee25-482b-9eb3-d13f3e78d16e

import Mathlib
import Definitions.Def_OnDemandCoord_Coordinates
import Theorems.Thm_OnDemandCoord_eq_13

set_option autoImplicit false

open MeasureTheory ProbabilityTheory OnDemandCoord
open scoped ENNReal

namespace OnDemandCoord.Eq15Proof

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

theorem tfrb_policy_and_noWaste {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (M : Model Ω P n) (Q : Fin n → ℝ) (s : ℝ) (β : Fin n → ℝ) (run : RunData n s)
    {T : ℕ} (hT : 2 ≤ T) :
    IsPolicy (M.tfrb Q s β run T) ∧ IsNoWaste (M.tfrb Q s β run T) := by
  have hdet : ∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (r : ℝ), 0 ≤ x → 0 ≤ r →
      IsFeasibleAlloc x r (priorityAlloc σ x r) ∧
      ∑ i, priorityAlloc σ x r i = min r (∑ i, x i) := by
    intro σ x r hx hr
    have hpref := prefix_sum σ x r hx hr n le_rfl
    have huniv : Finset.univ.filter (fun l : Fin n => (l : ℕ) < n) = Finset.univ :=
      Finset.filter_true_of_mem fun l _ => l.isLt
    rw [huniv] at hpref
    have htot : ∑ i, priorityAlloc σ x r i = min r (∑ i, x i) := by
      rw [← Equiv.sum_comp σ (priorityAlloc σ x r), ← Equiv.sum_comp σ x]
      exact hpref
    refine ⟨⟨fun i => ⟨le_min (hx i) (le_max_right _ _), min_le_left _ _⟩, ?_⟩, htot⟩
    rw [htot]
    exact min_le_left _ _
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
  exact ⟨⟨hmarkov, fun x r hx hr => hae_dirac_sum x r _ fun σ => (hdet σ x r hx hr).1⟩,
    fun x r hx hr => hae_dirac_sum x r _ fun σ => (hdet σ x r hx hr).2⟩

theorem platform_noWaste_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (M : Model Ω P n) (Q : Fin n → ℝ) (η : ℝ) (K : Contract n) (hβ : ∀ i, 0 < K.β i)
    (κ : Kernel ((Fin n → ℝ) × ℝ) (Fin n → ℝ)) (hκ : IsPolicy κ) (hnw : IsNoWaste κ) :
    M.platformProfit K η κ Q =
      M.p * ∑ i, (1 - K.m i) * M.mean Q i - M.C Q η + M.c * ∑ i, Q i + ∑ i, K.r i := by
  have : IsProbabilityMeasure P := M.isProb
  have : IsMarkovKernel κ := hκ.1
  have hG_nn : 0 ≤ M.G η := by
    rcases le_total η M.τl with hle | hge
    · rw [M.G_of_le η hle]
    · rw [← M.G_of_le M.τl le_rfl]; exact M.monotone_G hge
  have hS_nn : 0 ≤ M.S η := mul_nonneg M.N_pos.le hG_nn
  have hvac_nn : ∀ ω : Ω, 0 ≤ M.vacVec Q ω := fun _ _ => le_max_right _ _
  have hvac_meas : ∀ i : Fin n, Measurable (M.vac Q i) :=
    fun i => ((M.measurable_X i).sub_const (Q i)).max measurable_const
  have hvac_int : ∀ i : Fin n, Integrable (M.vac Q i) P := by
    intro i
    refine Integrable.mono' ((M.integrable_X i).sub (integrable_const (Q i))).norm
      (hvac_meas i).aestronglyMeasurable (ae_of_all P fun ω => ?_)
    simp only [Model.vac, Real.norm_eq_abs]
    rcases le_total (M.X i ω - Q i) 0 with hle | hge
    · rw [max_eq_right hle, abs_zero]; exact abs_nonneg _
    · rw [max_eq_left hge]; exact le_rfl
  have hV_meas : Measurable (fun ω : Ω => ∑ i, M.vac Q i ω) :=
    Finset.measurable_sum Finset.univ fun i _ => hvac_meas i
  have hV_int : Integrable (fun ω : Ω => ∑ i, M.vac Q i ω) P :=
    integrable_finsetSum Finset.univ fun i _ => hvac_int i
  have hmax_int : Integrable (fun ω : Ω => max (∑ i, M.vac Q i ω - M.S η) 0) P := by
    refine Integrable.mono' (hV_int.sub (integrable_const (M.S η))).norm
      ((hV_meas.sub_const (M.S η)).max measurable_const).aestronglyMeasurable
      (ae_of_all P fun ω => ?_)
    simp only [Real.norm_eq_abs]
    rcases le_total (∑ i, M.vac Q i ω - M.S η) 0 with hle | hge
    · rw [max_eq_right hle, abs_zero]; exact abs_nonneg _
    · rw [max_eq_left hge]; exact le_rfl
  have hai_int : ∀ (ω : Ω) (i : Fin n),
      Integrable (fun a : Fin n → ℝ => a i) (κ (M.vacVec Q ω, M.S η)) := by
    intro ω i
    refine Integrable.mono' (integrable_const (M.vac Q i ω))
      (measurable_pi_apply i).aestronglyMeasurable ?_
    filter_upwards [hκ.2 (M.vacVec Q ω) (M.S η) (hvac_nn ω) hS_nn] with a ha
    rw [Real.norm_eq_abs, abs_of_nonneg (ha.1 i).1]
    exact (ha.1 i).2
  have hexpA_int : ∀ i : Fin n,
      Integrable (fun ω : Ω => ∫ a, a i ∂κ (M.vacVec Q ω, M.S η)) P := by
    intro i
    have hpi : Measurable (fun a : Fin n → ℝ => a i) := measurable_pi_apply i
    have hsm : StronglyMeasurable (fun ω : Ω => ∫ a, a i ∂κ (M.vacVec Q ω, M.S η)) :=
      (hpi.stronglyMeasurable.integral_kernel (κ := κ)).comp_measurable
        ((M.measurable_vacVec Q).prodMk (measurable_const (a := M.S η)))
    refine Integrable.mono' (hvac_int i) hsm.aestronglyMeasurable (ae_of_all P fun ω => ?_)
    refine (norm_integral_le_integral_norm _).trans ?_
    have hbound : ∫ a, ‖a i‖ ∂κ (M.vacVec Q ω, M.S η) ≤
        ∫ _, M.vac Q i ω ∂κ (M.vacVec Q ω, M.S η) := by
      refine integral_mono_ae (hai_int ω i).norm (integrable_const _) ?_
      filter_upwards [hκ.2 (M.vacVec Q ω) (M.S η) (hvac_nn ω) hS_nn] with a ha
      rw [Real.norm_eq_abs, abs_of_nonneg (ha.1 i).1]
      exact (ha.1 i).2
    simpa [integral_const, probReal_univ] using hbound
  have hpay_eq : ∀ (i : Fin n) (a x : Fin n → ℝ),
      M.payment K i a x = (K.r i - M.p * K.m i * x i) + M.p * a i := by
    intro i a x
    unfold Model.payment Model.fixedRate Model.contingentPayment
    have hβi : K.β i ≠ 0 := (hβ i).ne'
    field_simp
    ring
  have hinner_i : ∀ (ω : Ω) (i : Fin n),
      (∫ a, M.payment K i a (M.vacVec Q ω) ∂κ (M.vacVec Q ω, M.S η)) =
        (K.r i - M.p * K.m i * M.vac Q i ω) +
          M.p * ∫ a, a i ∂κ (M.vacVec Q ω, M.S η) := by
    intro ω i
    simp_rw [hpay_eq i _ (M.vacVec Q ω)]
    rw [integral_add (integrable_const _) ((hai_int ω i).const_mul M.p),
      integral_const, probReal_univ, one_smul, integral_const_mul]
    rfl
  unfold Model.platformProfit Model.C
  have houter_i : ∀ i : Fin n,
      (∫ ω, ∫ a, M.payment K i a (M.vacVec Q ω) ∂κ (M.vacVec Q ω, M.S η) ∂P) =
        K.r i - M.p * K.m i * M.mean Q i +
          M.p * ∫ ω, (∫ a, a i ∂κ (M.vacVec Q ω, M.S η)) ∂P := by
    intro i
    simp_rw [hinner_i _ i]
    have hint1 : Integrable (fun ω : Ω => K.r i - M.p * K.m i * M.vac Q i ω) P :=
      (integrable_const _).sub ((hvac_int i).const_mul _)
    rw [integral_add hint1 ((hexpA_int i).const_mul M.p),
      integral_sub (integrable_const _) ((hvac_int i).const_mul _),
      integral_const, probReal_univ, one_smul, integral_const_mul, integral_const_mul]
    rfl
  simp_rw [houter_i]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← integral_finset_sum Finset.univ fun i _ => hexpA_int i]
  have hsum_in : ∀ ω : Ω,
      (∑ i, ∫ a, a i ∂κ (M.vacVec Q ω, M.S η)) =
        min (M.S η) (∑ i, M.vac Q i ω) := by
    intro ω
    rw [← integral_finsetSum Finset.univ fun i _ => hai_int ω i]
    have h1 := integral_congr_ae (hnw (M.vacVec Q ω) (M.S η) (hvac_nn ω) hS_nn)
    simpa [integral_const, probReal_univ, Model.vacVec] using h1
  simp_rw [hsum_in]
  have hmin_pt : ∀ ω : Ω,
      min (M.S η) (∑ i, M.vac Q i ω) =
        (∑ i, M.vac Q i ω) - max (∑ i, M.vac Q i ω - M.S η) 0 := by
    intro ω
    rcases le_total (M.S η) (∑ i, M.vac Q i ω) with hle | hge
    · rw [min_eq_left hle, max_eq_left (by linarith)]; ring
    · rw [min_eq_right hge, max_eq_right (by linarith)]; ring
  simp_rw [hmin_pt]
  rw [integral_sub hV_int hmax_int, integral_finset_sum Finset.univ fun i _ => hvac_int i]
  change (∑ i, K.r i) - (∑ i, M.p * K.m i * M.mean Q i) +
      M.p * ((∑ i, M.mean Q i) - ∫ ω, max (∑ i, M.vac Q i ω - M.S η) 0 ∂P) - η * M.S η =
    M.p * ∑ i, (1 - K.m i) * M.mean Q i -
      (M.p * ∫ ω, max (∑ i, M.vac Q i ω - M.S η) 0 ∂P + η * M.S η + M.c * ∑ i, Q i) +
      M.c * ∑ i, Q i + ∑ i, K.r i
  have hm1 : (∑ i, M.p * K.m i * M.mean Q i) = M.p * ∑ i, K.m i * M.mean Q i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have hm2 : ∑ i, (1 - K.m i) * M.mean Q i =
      (∑ i, M.mean Q i) - ∑ i, K.m i * M.mean Q i := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hm1, hm2]
  ring

end OnDemandCoord.Eq15Proof

open OnDemandCoord.Eq15Proof in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} (M : Model Ω P n)
    (Qp Qstar : Fin n → ℝ) (ηstar : ℝ) (hopt : M.IsSystemOptimum Qstar ηstar)
    (K : Contract n) (_hm : K.m = M.mParam Qstar)
    (_hβ : M.IsOptimalLP Qstar (M.S ηstar) K.β) (hpos : ∀ i, 0 < K.β i)
    (run : RunData n (M.S ηstar)) (T : ℕ) (hT : 2 ≤ T) :
    M.platformProfit K ηstar (M.tfrb Qstar (M.S ηstar) K.β run T) Qstar =
        M.p * ∑ i, (1 - K.m i) * M.mean Qstar i - M.C Qstar ηstar +
          M.c * ∑ i, Qstar i + ∑ i, K.r i ∧
      (M.FeeLower Qstar ηstar K.m K.r →
        0 ≤ M.platformProfit K ηstar (M.tfrb Qstar (M.S ηstar) K.β run T) Qstar) ∧
      ∀ i, M.FeeUpper Qp Qstar K.m K.r i →
        M.firmCost K i Qstar (M.tfrb Qstar (M.S ηstar) K.β run T) ηstar ≤ M.hp Qp i := by
  obtain ⟨hpol, hnw⟩ := tfrb_policy_and_noWaste M Qstar (M.S ηstar) K.β run hT
  have hprof := platform_noWaste_eq M Qstar ηstar K hpos _ hpol hnw
  refine ⟨hprof, ?_, ?_⟩
  · intro hfl
    unfold Model.FeeLower at hfl
    rw [hprof]
    linarith
  · intro i hfu
    unfold Model.FeeUpper at hfu
    rw [OnDemandCoord.eq_13 M K hpos i Qstar hopt.1 ηstar _ hpol]
    linarith
