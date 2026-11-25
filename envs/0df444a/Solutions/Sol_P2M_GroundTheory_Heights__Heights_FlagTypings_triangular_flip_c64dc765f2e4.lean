-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FlagTypings_triangular_flip_c64dc765f2e4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:07:07.013563+00:00
-- url     : https://prove2.me/submissions/fc07529d-57e7-40a8-a0c6-198077861dcc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_TrivBundleIsTwistedForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisor
import Theorems.Thm_GroundTheory_Arith_Iwasawa_IsDistinguished_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FlagTypings
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
set_option linter.unusedSectionVars false
variable {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.FlagTypings
theorem _root_.solution (w w' : Module.Basis (Fin N) Ω E)
    (h : ∀ i j : Fin N, i < j → w.repr (w' i) j = 0) :
    (∀ i j : Fin N, i < j → w'.repr (w i) j = 0) ∧ ∀ i, w.repr (w' i) i ≠ 0 := by
  have hA : (w.toMatrix w').BlockTriangular id := fun i j hji => by
    rw [Module.Basis.toMatrix_apply]
    exact h j i hji
  have : Invertible (w.toMatrix w') := w.invertibleToMatrix w'
  have hinv : (w.toMatrix w')⁻¹ = w'.toMatrix w :=
    Matrix.inv_eq_right_inv (w.toMatrix_mul_toMatrix_flip w')
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hB := Matrix.blockTriangular_inv_of_blockTriangular hA
    rw [hinv] at hB
    have := @hB j i hij
    rwa [Module.Basis.toMatrix_apply] at this
  · have hdet : (w.toMatrix w').det ≠ 0 :=
      (Matrix.isUnit_det_of_right_inverse (w.toMatrix_mul_toMatrix_flip w')).ne_zero
    rw [Matrix.det_of_isUpperTriangular hA] at hdet
    have := Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ _)
    rwa [Module.Basis.toMatrix_apply] at this
end GroundTheory.Heights₂.Heights.FlagTypings
