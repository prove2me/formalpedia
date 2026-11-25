-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.valuation_det_cosetCoordinateMatrix_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:46:06.44713+00:00
-- url     : https://prove2.me/submissions/cec8b01c-3d00-4105-9482-9cc55f2f242d

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitDetOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetLeOneOfEntriesIntegral
import Theorems.Thm_ReciprocityTheory_PGsh_L2_cosetCoordinateMatrix_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N) [DecidablePred (· ∈ K)]
    (β : Matrix K K C) (hβ : IsUnit β.det)
    (hAK : AA.carrier.map (resK (R := R) K) = Submodule.span R (Set.range fun j k => β k j))
    (f : K → N → C) (x : N) (k : K) :
    v (h3mm K β f (x + k)).det = v (h3mm K β f x).det := by
  rw [cosetCoordinateMatrix_add K β hβ f x k, Matrix.det_mul, map_mul]
  suffices h : v (h3T K β k).det = 1 by rw [h, mul_one]
  have hT : h3T K β k = (β⁻¹ * β.submatrix (Equiv.addLeft k) id)ᵀ := by
    ext l l'
    simp [h3T, Matrix.mulVec, dotProduct, Matrix.mul_apply]
  rw [hT, Matrix.det_transpose, Matrix.det_mul, Matrix.det_permute, Matrix.det_nonsing_inv]
  have hd : β.det ≠ 0 := hβ.ne_zero
  have hs : v ((Equiv.Perm.sign (Equiv.addLeft k) : ℤ) : C) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.addLeft k)) with h | h <;>
      simp [h, Valuation.map_neg]
  rw [Ring.inverse_eq_inv', map_mul, map_mul, hs, one_mul, map_inv₀, inv_mul_cancel₀]
  exact (Valuation.ne_zero_iff v).mpr hd
end ReciprocityTheory.PGsh.L2
