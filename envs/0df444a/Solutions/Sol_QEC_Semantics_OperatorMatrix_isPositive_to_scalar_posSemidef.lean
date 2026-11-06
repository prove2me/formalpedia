-- Prove2me | solution 1 for QEC.Semantics.OperatorMatrix.isPositive_to_scalar_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:36:35.925567+00:00
-- url     : https://prove2.me/submissions/9b0fc68a-e212-4a04-9d61-dcb7f3e66ecd

import Mathlib
import Definitions.Def_QEC_Semantics_Core_Definitions
import Theorems.Thm_QEC_Semantics_OperatorMatrix_scalarMatrix_isHermitian
import Theorems.Thm_QEC_Semantics_OperatorMatrix_scalarMatrix_quadratic_eq_block

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct ComplexOrder
open QEC.Semantics.OperatorMatrix
variable {n : Nat} {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
namespace QEC.Semantics.OperatorMatrix
theorem _root_.solution {β : Type*} [Fintype β]
    (M : OperatorMatrix n H) (hM : IsPositive M)
    (b : OrthonormalBasis β Complex H) :
    (scalarMatrix M b).PosSemidef := by
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (scalarMatrix_isHermitian M hM b) ?_
  intro c
  rw [RCLike.nonneg_iff]
  constructor
  · rw [scalarMatrix_quadratic_eq_block]
    exact hM.2 (fun i => ∑ p : β, star (c (i, p)) • b p)
  · exact Matrix.IsHermitian.im_star_dotProduct_mulVec_self
      (scalarMatrix_isHermitian M hM b) c
end QEC.Semantics.OperatorMatrix
