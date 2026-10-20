-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P59.admissibleControlAlgebras
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T04:02:28.552507+00:00
-- url     : https://prove2.me/submissions/e0f20fbb-d520-4443-aed9-1e10f092c6e2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P59

noncomputable section

open scoped Matrix ComplexOrder

open scoped Matrix

open QAlgorithms.Papers.Independent.Information100.P59 in
noncomputable def g53h_Rl : Vec →ₗ[ℝ] Mat where
  toFun := rotationGenerator
  map_add' u v := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [rotationGenerator] <;> ring
  map_smul' c u := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [rotationGenerator]

open QAlgorithms.Papers.Independent.Information100.P59 in
lemma g53h_R_cross (u v : Vec) :
    rotationGenerator u * rotationGenerator v - rotationGenerator v * rotationGenerator u =
      rotationGenerator (u ⨯₃ v) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rotationGenerator, Matrix.mul_apply, Fin.sum_univ_three, crossProduct] <;> ring

open QAlgorithms.Papers.Independent.Information100.P59 in
lemma g53h_R_inj : Function.Injective rotationGenerator := by
  intro u v h
  have h1 := congrFun (congrFun h 2) 1
  have h2 := congrFun (congrFun h 0) 2
  have h3 := congrFun (congrFun h 1) 0
  simp [rotationGenerator] at h1 h2 h3
  funext k; fin_cases k <;> simp <;> linarith

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P59

attribute [local instance 100] LieRing.ofAssociativeRing

/-- arXiv:2610.00046v1 PDF p.9, Remark 3.2. The control algebra is computed
from the finite coherent generating list; no menu hypothesis is imposed on that list. -/
theorem solution (axes : Finset Vec) :
    let C := LieSubalgebra.lieSpan ℝ Mat (rotationGenerator '' (axes : Set Vec))
    C.toSubmodule = ⊥ ∨
      (∃ n : Vec, (∑ j, n j^2) = 1 ∧
        C.toSubmodule = Submodule.span ℝ {rotationGenerator n}) ∨
      C.toSubmodule = Submodule.span ℝ (Set.range rotationGenerator) := by
  intro C
  have hlie : ∀ x y : Mat, ⁅x, y⁆ = x * y - y * x := fun x y => Ring.lie_def x y
  have hRl : ∀ u, g53h_Rl u = rotationGenerator u := fun u => rfl
  by_cases hfull : ∃ u ∈ axes, ∃ v ∈ axes, u ⨯₃ v ≠ 0
  · right; right
    obtain ⟨u, hu, v, hv, huv⟩ := hfull
    have hrange : Submodule.span ℝ (Set.range rotationGenerator) = LinearMap.range g53h_Rl := by
      have : Set.range rotationGenerator = Set.range g53h_Rl := rfl
      rw [this, ← LinearMap.coe_range, Submodule.span_eq]
    let K : LieSubalgebra ℝ Mat :=
      { Submodule.span ℝ (Set.range rotationGenerator) with
        lie_mem' := by
          intro x y hx hy
          change x ∈ Submodule.span ℝ (Set.range rotationGenerator) at hx
          change y ∈ Submodule.span ℝ (Set.range rotationGenerator) at hy
          change ⁅x, y⁆ ∈ Submodule.span ℝ (Set.range rotationGenerator)
          rw [hrange] at hx hy ⊢
          obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy
          rw [hlie, hRl, hRl, g53h_R_cross]; exact ⟨_, rfl⟩ }
    have hle : C.toSubmodule ≤ Submodule.span ℝ (Set.range rotationGenerator) := by
      have : C ≤ K := by
        rw [LieSubalgebra.lieSpan_le]
        rintro _ ⟨w, _, rfl⟩
        exact Submodule.subset_span ⟨w, rfl⟩
      exact this
    have hRu : rotationGenerator u ∈ C := LieSubalgebra.subset_lieSpan ⟨u, hu, rfl⟩
    have hRv : rotationGenerator v ∈ C := LieSubalgebra.subset_lieSpan ⟨v, hv, rfl⟩
    have hRw : rotationGenerator (u ⨯₃ v) ∈ C := by
      rw [← g53h_R_cross, ← hlie]; exact C.lie_mem hRu hRv
    let f : Fin 3 → Vec := ![u, v, u ⨯₃ v]
    have hli : LinearIndependent ℝ f := by
      have hdet : (Matrix.of f).det ≠ 0 := by
        have : (Matrix.of f).det = (u ⨯₃ v) ⬝ᵥ (u ⨯₃ v) := by
          rw [show Matrix.of f = ![u, v, u ⨯₃ v] from rfl, ← triple_product_eq_det,
            triple_product_permutation, triple_product_permutation]
        rw [this]; intro h; exact huv (dotProduct_self_eq_zero.1 h)
      exact Matrix.linearIndependent_rows_of_det_ne_zero hdet
    have hli2 : LinearIndependent ℝ (g53h_Rl ∘ f) :=
      hli.map' g53h_Rl (LinearMap.ker_eq_bot.2 g53h_R_inj)
    have hspan_le : Submodule.span ℝ (Set.range (g53h_Rl ∘ f)) ≤ C.toSubmodule := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      fin_cases k
      · exact hRu
      · exact hRv
      · exact hRw
    have hfin : Module.finrank ℝ (Submodule.span ℝ (Set.range rotationGenerator)) ≤
        Module.finrank ℝ (Submodule.span ℝ (Set.range (g53h_Rl ∘ f))) := by
      rw [finrank_span_eq_card hli2, hrange]
      simpa using LinearMap.finrank_range_le g53h_Rl
    have := Submodule.eq_of_le_of_finrank_le (hspan_le.trans hle) hfin
    exact le_antisymm hle (this ▸ hspan_le)
  · push Not at hfull
    by_cases hz : ∀ u ∈ axes, u = 0
    · left
      rw [eq_bot_iff]
      have : C ≤ ⊥ := by
        rw [LieSubalgebra.lieSpan_le]
        rintro _ ⟨w, hw, rfl⟩
        rw [hz w hw]
        have : rotationGenerator 0 = 0 := by rw [← hRl, map_zero]
        rw [this]; exact (⊥ : LieSubalgebra ℝ Mat).zero_mem
      intro x hx
      have := this hx
      simpa using this
    · right; left
      push Not at hz
      obtain ⟨w, hw, hw0⟩ := hz
      have hww : 0 < w ⬝ᵥ w := by
        have h0 : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
        rcases lt_or_eq_of_le h0 with h | h
        · exact h
        · exact absurd (dotProduct_self_eq_zero.1 h.symm) hw0
      set r := Real.sqrt (w ⬝ᵥ w) with hr
      have hr0 : 0 < r := Real.sqrt_pos.2 hww
      refine ⟨r⁻¹ • w, ?_, ?_⟩
      · have : (∑ j, (r⁻¹ • w) j ^ 2) = r⁻¹ ^ 2 * (w ⬝ᵥ w) := by
          simp [dotProduct, Finset.mul_sum, Fin.sum_univ_three]; ring
        rw [this, inv_pow, hr, Real.sq_sqrt hww.le, inv_mul_cancel₀ hww.ne']
      · have hRn : rotationGenerator (r⁻¹ • w) = r⁻¹ • rotationGenerator w := by
          rw [← hRl, map_smul]; rfl
        have hpar : ∀ u ∈ axes, u = ((u ⬝ᵥ w) / (w ⬝ᵥ w)) • w := by
          intro u hu
          have h0 := cross_cross_eq_smul_sub_smul u w w
          rw [hfull u hu w hw, LinearMap.map_zero₂] at h0
          have : (w ⬝ᵥ w) • u = (u ⬝ᵥ w) • w := by
            have := sub_eq_zero.1 h0.symm; exact this.symm
          rw [div_eq_mul_inv, mul_comm, mul_smul, ← this, smul_smul, inv_mul_cancel₀ hww.ne', one_smul]
        let K : LieSubalgebra ℝ Mat :=
          { Submodule.span ℝ {rotationGenerator (r⁻¹ • w)} with
            lie_mem' := by
              intro x y hx hy
              change x ∈ Submodule.span ℝ {rotationGenerator (r⁻¹ • w)} at hx
              change y ∈ Submodule.span ℝ {rotationGenerator (r⁻¹ • w)} at hy
              change ⁅x, y⁆ ∈ Submodule.span ℝ {rotationGenerator (r⁻¹ • w)}
              obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
              obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hy
              rw [smul_lie, lie_smul, lie_self, smul_zero, smul_zero]
              exact Submodule.zero_mem _ }
        apply le_antisymm
        · have : C ≤ K := by
            rw [LieSubalgebra.lieSpan_le]
            rintro _ ⟨u, hu, rfl⟩
            change rotationGenerator u ∈ Submodule.span ℝ {rotationGenerator (r⁻¹ • w)}
            rw [Submodule.mem_span_singleton]
            refine ⟨((u ⬝ᵥ w) / (w ⬝ᵥ w)) * r, ?_⟩
            rw [hRn, smul_smul, mul_assoc, mul_inv_cancel₀ hr0.ne', mul_one]
            conv_rhs => rw [hpar u hu]
            exact (g53h_Rl.map_smul _ _).symm
          exact this
        · rw [Submodule.span_le, Set.singleton_subset_iff, hRn]
          exact C.smul_mem _ (LieSubalgebra.subset_lieSpan ⟨w, hw, rfl⟩)



end

