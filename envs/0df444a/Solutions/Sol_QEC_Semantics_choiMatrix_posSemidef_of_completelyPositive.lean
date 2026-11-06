-- Prove2me | solution 1 for QEC.Semantics.choiMatrix_posSemidef_of_completelyPositive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:35:23.101609+00:00
-- url     : https://prove2.me/submissions/1544af47-ce0f-42c6-92be-b38ab8db51d2

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Channels_Choi
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnitBlock_isPositive
import Theorems.Thm_QEC_Semantics_OperatorMatrix_isPositive_to_scalar_posSemidef


set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
namespace QEC.Semantics
theorem _root_.solution {n : Nat} {βK : Type*}
    [Fintype βK]
    (Φ : Operator H →ₗ[Complex] Operator K)
    (hΦ : CompletelyPositive Φ)
    (bH : OrthonormalBasis (Fin n) Complex H)
    (bK : OrthonormalBasis βK Complex K) :
    (choiMatrix Φ bH bK).PosSemidef := by
  classical
  exact OperatorMatrix.isPositive_to_scalar_posSemidef
    (OperatorMatrix.map Φ (OperatorMatrix.matrixUnitBlock bH))
    (hΦ n (OperatorMatrix.matrixUnitBlock bH)
      (OperatorMatrix.matrixUnitBlock_isPositive bH))
    bK
end QEC.Semantics
