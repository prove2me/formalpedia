-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.FrobeniusGroupField.sg_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:31:11.018445+00:00
-- url     : https://prove2.me/submissions/fdfa549d-25ef-41c1-a9a0-ef18aa8017b3

import Definitions.Def_ReciprocityTheory_DualLattices_EigPowEqOne
import Definitions.Def_ReciprocityTheory_DualLattices_IsAdicCompleteOfBasis
import Definitions.Def_ReciprocityTheory_DualLattices_SgAlgebraMap
import Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusGroupField_isDomain


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix Polynomial
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.FrobeniusGroupField
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.FrobeniusGroupField
theorem _root_.solution (hv : v.Integers R) {p : ℕ} [Fact p.Prime]
    [Algebra ℤ_[p] R] {n : Type} [Fintype n] [DecidableEq n] {ι : Type}
    {O : Type} [CommRing O] [Algebra ℤ_[p] O] (ρ : O →ₐ[ℤ_[p]] Matrix n n ℤ_[p])
    (εT : ι → Matrix n n R) (sg : ι → O →+* R)
    (heig : ∀ a j, (ρ a).map (algebraMap ℤ_[p] R) * εT j = sg j a • εT j) (j : ι) (hj : εT j ≠ 0)
    (z : ℤ_[p]) : sg j (algebraMap ℤ_[p] O z) = algebraMap ℤ_[p] R z := by
  haveI : IsDomain R := hv.hom_inj.isDomain (algebraMap R C)
  have hm : (ρ (algebraMap ℤ_[p] O z)).map (algebraMap ℤ_[p] R) = algebraMap ℤ_[p] (Matrix n n R) z := by
    ext i k
    rw [AlgHom.commutes, Matrix.map_apply, Matrix.algebraMap_matrix_apply, Matrix.algebraMap_matrix_apply]
    split_ifs <;> simp
  have h := heig (algebraMap ℤ_[p] O z) j
  rw [hm, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, ← algebraMap_smul R z (εT j)] at h
  have h2 : (algebraMap ℤ_[p] R z - sg j (algebraMap ℤ_[p] O z)) • εT j = 0 := by
    rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact (sub_eq_zero.mp h3).symm
  · exact absurd h3 hj
end ReciprocityTheory.PGsh.Up.FrobeniusGroupField
