-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P31.lemma29_choiBasis
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T06:17:06.42348+00:00
-- url     : https://prove2.me/submissions/87ae50a1-1ba9-45cc-b863-bf4c6ca26a39

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_corollary22_basis
noncomputable section
open QAlgorithms.Papers.Independent.Extend50.P31
open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)
open QAlgorithms.Papers.Independent.Frontier18.P17 (hs res)
open scoped Matrix ComplexConjugate
set_option backward.isDefEq.respectTransparency false
variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}
private lemma hs_coordinates (X Y : Mat n) : hs X Y = ∑ p : Fin n × Fin n, conj (rowVec X p) * rowVec Y p := by
  simp [hs,res,PiLp.inner_apply,RCLike.inner_apply,rowVec,mul_comm]
private lemma hs_transpose (X Y : Mat n) : hs Xᵀ Yᵀ = hs X Y := by
  simp only [hs_coordinates,rowVec,Fintype.sum_prod_type,Matrix.transpose_apply]
  exact Finset.sum_comm


set_option autoImplicit false

set_option autoImplicit false
open QAlgorithms.Papers.Independent.Extend50.P31
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq



open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}

/-- PDF p.15, Lemma 29 Eq.(75), transpose without complex conjugation. -/
theorem solution (D : Data G A n) (P : Pivots D) :
    (∀ r s, (∑ p, conj (choiVector D P r p) * choiVector D P s p) =
      if r = s then 1 else 0) ∧
    Submodule.span ℂ (Set.range (choiVector D P)) = ⊤ := by
  obtain ⟨_,horth,hspan⟩ := corollary22_basis D P
  constructor
  · intro r s
    change (∑ p, conj (rowVec (eigenmatrix D P r)ᵀ p) * rowVec (eigenmatrix D P s)ᵀ p) = _
    rw [← hs_coordinates,hs_transpose,horth]
  · let F : Mat n →ₗ[ℂ] ((Fin n × Fin n) → ℂ) :=
      { toFun := fun X => rowVec Xᵀ
        map_add' := by intro X Y; simp [Matrix.transpose_add]
        map_smul' := by intro c X; simp [Matrix.transpose_smul] }
    have hsurj : Function.Surjective F := by
      intro v
      refine ⟨(rowVec.symm v)ᵀ,?_⟩
      simp [F]
    have hm : (Submodule.span ℂ (Set.range (eigenmatrix D P))).map F =
        Submodule.span ℂ (Set.range (choiVector D P)) := by
      rw [Submodule.map_span,← Set.range_comp]
      rfl
    rw [hspan,Submodule.map_top,LinearMap.range_eq_top.mpr hsurj] at hm
    exact hm.symm
