-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.matrixElement_zero_of_scopedByWeight_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:46:30.973895+00:00
-- url     : https://prove2.me/submissions/fdb15ed3-215e-43bf-90a3-4476a68c29a4

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_syndromeSeparatedByCheckSet_of_scopedByWeight_pair
import Theorems.Thm_QEC_Coding_PauliSymplectic_matrixElement_zero_of_syndromeSeparatedByCheckSet

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open Classical
open scoped BigOperators
universe u w
open QEC.Coding.PauliSymplectic
variable {ι : Type u} [Fintype ι]
variable [DecidableEq ι]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {dX dZ t : Nat}
    (hminX : MinimumDistance zCode.dual dX)
    (hminZ : MinimumDistance xCode.dual dZ)
    (hbound : 2 * t < min dX dZ)
    {E F : Binary ι}
    (hE : E ∈ scopedByWeight (ι := ι) t)
    (hF : F ∈ scopedByWeight (ι := ι) t)
    (hnontrivial :
      (binaryMul (binaryDagger E) F).vector.xPart ≠ 0 ∨
      (binaryMul (binaryDagger E) F).vector.zPart ≠ 0)
    {ψ φ : Semantics.Qubit.QubitRegister ι}
    (hψ : ψ ∈ (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier)
    (hφ : φ ∈ (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier) :
    inner Complex (toQubitOperator E ψ) (toQubitOperator F φ) = 0 :=
  matrixElement_zero_of_syndromeSeparatedByCheckSet xCode zCode hdual
    (syndromeSeparatedByCheckSet_of_scopedByWeight_pair
      xCode zCode hminX hminZ hbound hE hF hnontrivial)
    hψ hφ
end QEC.Coding.PauliSymplectic
