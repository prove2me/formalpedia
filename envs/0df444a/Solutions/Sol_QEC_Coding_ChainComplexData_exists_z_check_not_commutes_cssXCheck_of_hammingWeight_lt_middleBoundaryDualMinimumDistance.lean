-- Prove2me | solution 1 for QEC.Coding.ChainComplexData.exists_z_check_not_commutes_cssXCheck_of_hammingWeight_lt_middleBoundaryDualMinimumDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:12:31.587064+00:00
-- url     : https://prove2.me/submissions/5721e65b-ce41-455d-a993-0a8df078e6cb

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_exists_z_check_not_commutes_cssXCheck_of_hammingWeight_lt_dualMinimumDistance

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
    {dX : Nat}
    (hminX : MinimumDistance K.middleBoundaryCode.dual dX)
    {x : Word (ZMod 2) ι} (hx0 : x ≠ 0) (hxlt : HammingWeight x < dX) :
    ∃ z, z ∈ K.middleBoundaryCode.carrier ∧
      ¬ PauliSymplectic.Commutes
        (PauliSymplectic.cssXCheck x) (PauliSymplectic.cssZCheck z) := by
  exact
    PauliSymplectic.exists_z_check_not_commutes_cssXCheck_of_hammingWeight_lt_dualMinimumDistance
      K.middleBoundaryCode hminX hx0 hxlt
end QEC.Coding.ChainComplexData
