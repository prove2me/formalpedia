-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P40.sl_states_full_measure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:58:08.661803+00:00
-- url     : https://prove2.me/submissions/f2eaf313-922b-4b72-8d7e-4bc3988f63d2

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P40
noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P40

open scoped Matrix.Norms.Frobenius

end QAlgorithms.Papers.Independent.Advance50.P40

open QAlgorithms.Papers.Independent.Advance50.P40
open scoped Matrix.Norms.Frobenius

section s110s
variable {n m : ℕ}

/-- Hermitian matrices as a real subspace. -/
def s110sH (n m : ℕ) : Submodule ℝ (JointMatrix n m) where
  carrier := {σ | σ.conjTranspose = σ}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [Matrix.conjTranspose_add, ha, hb]
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_ofPred_eq] at *
    rw [Matrix.conjTranspose_smul, ha, star_trivial]

def s110sV0 (n m : ℕ) : Submodule ℝ (JointMatrix n m) where
  carrier := {σ | σ.conjTranspose = σ ∧ σ.trace = 0}
  add_mem' := by
    intro a b ha hb
    exact ⟨by rw [Matrix.conjTranspose_add, ha.1, hb.1], by rw [Matrix.trace_add, ha.2, hb.2, add_zero]⟩
  zero_mem' := ⟨by simp, by simp⟩
  smul_mem' := by
    intro c a ha
    exact ⟨by rw [Matrix.conjTranspose_smul, ha.1, star_trivial],
      by rw [Matrix.trace_smul, ha.2, smul_zero]⟩

def s110stb (i j : Fin n) (σ : JointMatrix n m) : ℂ := ∑ a, σ (i, a) (j, a)

def s110sV (i j : Fin n) : Submodule ℝ (JointMatrix n m) where
  carrier := {σ | σ.conjTranspose = σ ∧ σ.trace = 0 ∧ s110stb i j σ = 0}
  add_mem' := by
    intro a b ha hb
    refine ⟨by rw [Matrix.conjTranspose_add, ha.1, hb.1], by rw [Matrix.trace_add, ha.2.1, hb.2.1, add_zero], ?_⟩
    have h1 := ha.2.2; have h2 := hb.2.2
    simp only [s110stb, Matrix.add_apply, Finset.sum_add_distrib] at *
    rw [h1, h2, add_zero]
  zero_mem' := ⟨by simp, by simp, by simp [s110stb]⟩
  smul_mem' := by
    intro c a ha
    refine ⟨by rw [Matrix.conjTranspose_smul, ha.1, star_trivial],
      by rw [Matrix.trace_smul, ha.2.1, smul_zero], ?_⟩
    have h1 := ha.2.2
    simp only [s110stb, Matrix.smul_apply, ← Finset.smul_sum] at *
    rw [h1, smul_zero]

lemma s110s_finrank_H : Module.finrank ℝ (s110sH n m) ≤ (n * m) ^ 2 := by
  let f : JointMatrix n m →ₗ[ℝ] ((Fin n × Fin m) × (Fin n × Fin m) → ℝ) :=
    { toFun := fun σ p => (σ p.1 p.2).re + (σ p.1 p.2).im
      map_add' := by intro a b; funext p; simp; ring
      map_smul' := by intro c a; funext p; simp; ring }
  have hinj : Function.Injective (f.comp (s110sH n m).subtype) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro δ hδ
    have hH : (δ : JointMatrix n m).conjTranspose = δ := δ.2
    ext x y
    have h1 := congrFun hδ (x, y)
    have h2 := congrFun hδ (y, x)
    have h3 : (δ : JointMatrix n m) y x = star ((δ : JointMatrix n m) x y) := by
      conv_lhs => rw [← hH]
      rfl
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply] at h1 h2
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h1 h2
    rw [h3] at h2
    simp only [Complex.star_def, Complex.conj_re, Complex.conj_im] at h2
    simp only [Submodule.coe_zero, Matrix.zero_apply]
    apply Complex.ext <;> simp <;> linarith
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fintype_fun_eq_card] at this
  simpa [Fintype.card_prod, Fintype.card_fin, sq] using this

lemma s110s_tb_single (i j k : Fin n) (hk : k ≠ i) (a0 : Fin m) :
    s110stb i j (Matrix.single (k, a0) (k, a0) (1 : ℂ) : JointMatrix n m) = 0 := by
  simp only [s110stb, Matrix.single_apply]
  apply Finset.sum_eq_zero
  intro a _
  rw [if_neg]
  rintro ⟨h1, -⟩
  exact hk (congrArg Prod.fst h1)

lemma s110s_finrank_V [NeZero m] (i j k : Fin n) (hk : k ≠ i) :
    Module.finrank ℝ (s110sV (m := m) i j) + 2 ≤ (n * m) ^ 2 := by
  have h01 : s110sV0 n m < s110sH n m := by
    rw [SetLike.lt_iff_le_and_exists]
    refine ⟨fun σ hσ => hσ.1, 1, by simp [s110sH], ?_⟩
    rintro ⟨-, h⟩
    rw [Matrix.trace_one] at h
    simp at h
    exact h.elim (fun h => by subst h; exact k.elim0) (NeZero.ne m)
  have h12 : s110sV (m := m) i j < s110sV0 n m := by
    rw [SetLike.lt_iff_le_and_exists]
    refine ⟨fun σ hσ => ⟨hσ.1, hσ.2.1⟩, ?_⟩
    by_cases hij : i = j
    · subst hij
      refine ⟨Matrix.single (i, 0) (i, 0) (1 : ℂ) - Matrix.single (k, 0) (k, 0) 1, ⟨?_, ?_⟩, ?_⟩
      · simp [Matrix.conjTranspose_sub]
      · simp [Matrix.trace_sub]
      · rintro ⟨-, -, h⟩
        simp only [s110stb, Matrix.sub_apply, Finset.sum_sub_distrib] at h
        have h2 := s110s_tb_single (m := m) i i k hk 0
        simp only [s110stb] at h2
        rw [h2, sub_zero] at h
        simp [Matrix.single_apply] at h
    · refine ⟨Matrix.single (i, 0) (j, 0) (1 : ℂ) + Matrix.single (j, 0) (i, 0) 1, ⟨?_, ?_⟩, ?_⟩
      · simp [Matrix.conjTranspose_add, add_comm]
      · rw [Matrix.trace_add, Matrix.trace_single_eq_of_ne _ _ _ (by simp [Prod.ext_iff, hij]),
          Matrix.trace_single_eq_of_ne _ _ _ (by simp [Prod.ext_iff, Ne.symm hij]), add_zero]
      · rintro ⟨-, -, h⟩
        simp [s110stb, Matrix.add_apply, Finset.sum_add_distrib, Matrix.single_apply, hij,
          Ne.symm hij] at h
  have a := Submodule.finrank_lt_finrank_of_lt h01
  have b := Submodule.finrank_lt_finrank_of_lt h12
  have c := s110s_finrank_H (n := n) (m := m)
  omega

lemma s110s_dimH_V (i j : Fin n) :
    dimH (s110sV (m := m) i j : Set (JointMatrix n m)) = Module.finrank ℝ (s110sV (m := m) i j) := by
  rw [← Real.dimH_univ_eq_finrank, ← Isometry.dimH_image (f := Subtype.val) (fun _ _ => rfl), Set.image_univ,
    Subtype.range_coe]

end s110s

theorem solution (n m : ℕ) [NeZero n] [NeZero m] :
    letI jointMetric : EMetricSpace (JointMatrix n m) := inferInstance
    letI jointMeasurable : MeasurableSpace (JointMatrix n m) :=
      @borel (JointMatrix n m) jointMetric.toUniformSpace.toTopologicalSpace
    (@MeasureTheory.Measure.hausdorffMeasure (JointMatrix n m)
      jointMetric jointMeasurable ⟨rfl⟩ (((n * m) ^ 2 - 1 : ℕ) : ℝ))
      {rho | QAlgorithms.IsDensityMatrix rho ∧ ¬ IsSLState rho} = 0 := by
  letI : MeasurableSpace (JointMatrix n m) :=
    @borel _ (inferInstance : EMetricSpace (JointMatrix n m)).toUniformSpace.toTopologicalSpace
  haveI : @BorelSpace (JointMatrix n m)
      (inferInstance : EMetricSpace (JointMatrix n m)).toUniformSpace.toTopologicalSpace _ := ⟨rfl⟩
  have hd : ((((n * m) ^ 2 - 1 : ℕ) : ℝ)) = (((((n * m) ^ 2 - 1 : ℕ)) : NNReal) : ℝ) :=
    (NNReal.coe_natCast _).symm
  have key : MeasureTheory.Measure.hausdorffMeasure (((n * m) ^ 2 - 1 : ℕ) : ℝ)
      {rho : JointMatrix n m | QAlgorithms.IsDensityMatrix rho ∧ ¬ IsSLState rho} = 0 := by
    have hsub : {rho : JointMatrix n m | QAlgorithms.IsDensityMatrix rho ∧ ¬ IsSLState rho} ⊆
        ⋃ i : Fin n, ⋃ j : Fin n,
          {rho : JointMatrix n m | QAlgorithms.IsDensityMatrix rho ∧ s110stb i j rho = 0} := by
      rintro ρ ⟨hρ, hns⟩
      simp only [IsSLState, not_forall, not_or] at hns
      obtain ⟨i, j, -, htr⟩ := hns
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
      refine ⟨i, j, hρ, ?_⟩
      simpa [bathBlock, Matrix.trace, s110stb] using htr
    refine MeasureTheory.measure_mono_null hsub ?_
    refine MeasureTheory.measure_iUnion_null fun i => MeasureTheory.measure_iUnion_null fun j => ?_
    by_cases hk : ∃ k : Fin n, k ≠ i
    · obtain ⟨k, hk⟩ := hk
      set ρ0 : JointMatrix n m := Matrix.single (k, 0) (k, 0) 1
      have hT : {rho : JointMatrix n m | QAlgorithms.IsDensityMatrix rho ∧ s110stb i j rho = 0} ⊆
          (IsometryEquiv.addLeft ρ0) '' (s110sV (m := m) i j : Set (JointMatrix n m)) := by
        rintro ρ ⟨hρ, htb⟩
        refine ⟨ρ - ρ0, ⟨?_, ?_, ?_⟩, by simp⟩
        · rw [Matrix.conjTranspose_sub, hρ.1.1.eq]
          simp [ρ0]
        · rw [Matrix.trace_sub, hρ.2]
          simp [ρ0]
        · have h0 := s110s_tb_single (m := m) i j k hk 0
          simp only [s110stb, Matrix.sub_apply, Finset.sum_sub_distrib] at h0 htb ⊢
          rw [htb, h0, sub_zero]
      rw [hd]
      apply hausdorffMeasure_of_dimH_lt
      refine lt_of_le_of_lt (dimH_mono hT) ?_
      rw [IsometryEquiv.dimH_image, s110s_dimH_V]
      have hf := s110s_finrank_V (m := m) i j k hk
      have hpos : 1 ≤ (n * m) ^ 2 := by omega
      rw [ENNReal.coe_natCast]
      exact_mod_cast (by omega : Module.finrank ℝ (s110sV (m := m) i j) < (n * m) ^ 2 - 1)
    · push Not at hk
      convert MeasureTheory.measure_empty (μ := MeasureTheory.Measure.hausdorffMeasure
        (((n * m) ^ 2 - 1 : ℕ) : ℝ) (X := JointMatrix n m))
      ext ρ
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hρ htb
      have hj : j = i := hk j
      subst hj
      have htr := hρ.2
      rw [Matrix.trace, Fintype.sum_prod_type, Fintype.sum_eq_single j (fun k hk' => absurd (hk k) hk')]
        at htr
      simp only [s110stb, Matrix.diag] at htb htr
      rw [htb] at htr
      exact zero_ne_one htr
  exact key

end
