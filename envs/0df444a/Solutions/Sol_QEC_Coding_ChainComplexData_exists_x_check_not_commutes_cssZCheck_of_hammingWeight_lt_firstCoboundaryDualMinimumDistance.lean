-- Prove2me | solution 1 for QEC.Coding.ChainComplexData.exists_x_check_not_commutes_cssZCheck_of_hammingWeight_lt_firstCoboundaryDualMinimumDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:12:32.515163+00:00
-- url     : https://prove2.me/submissions/011bfc95-dab6-4c00-aa14-a605a3463ca4

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_exists_x_check_not_commutes_cssZCheck_of_hammingWeight_lt_dualMinimumDistance

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open Classical
open scoped BigOperators
universe u w
open QEC.Coding.ChainComplexData
namespace QEC.Coding.ChainComplexData
theorem _root_.solution
    {ι κ C2 : Type u} [Fintype ι] [Fintype κ]
    [AddCommGroup C2] [Module (ZMod 2) C2]
    (K : ChainComplexData
      (ZMod 2) (Word (ZMod 2) κ) (Word (ZMod 2) ι) C2)
    {dZ : Nat}
    (hminZ : MinimumDistance K.firstCoboundaryCheckCode.dual dZ)
    {z : Word (ZMod 2) ι} (hz0 : z ≠ 0) (hzlt : HammingWeight z < dZ) :
    ∃ x, x ∈ K.firstCoboundaryCheckCode.carrier ∧
      ¬ PauliSymplectic.Commutes
        (PauliSymplectic.cssZCheck z) (PauliSymplectic.cssXCheck x) := by
  exact
    PauliSymplectic.exists_x_check_not_commutes_cssZCheck_of_hammingWeight_lt_dualMinimumDistance
      K.firstCoboundaryCheckCode hminZ hz0 hzlt
end QEC.Coding.ChainComplexData
