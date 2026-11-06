-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.checkDistinguishes_cssZCheck_of_hammingWeight_lt_dualMinimumDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:27:13.069528+00:00
-- url     : https://prove2.me/submissions/4dd00f3f-2ff3-48bc-9e91-eee75e1309d2

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
open QEC.Coding.PauliSymplectic
variable {ι : Type u} [Fintype ι]
variable [DecidableEq ι]
omit [DecidableEq ι]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution
    (xCode zCode : LinearCode (ZMod 2) ι) {dZ : Nat}
    (hminZ : MinimumDistance xCode.dual dZ)
    {z : Word (ZMod 2) ι} (hz0 : z ≠ 0) (hzlt : HammingWeight z < dZ) :
    checkDistinguishes (binaryCSSCheckSet xCode zCode) (cssZCheck z) := by
  rcases
      exists_x_check_not_commutes_cssZCheck_of_hammingWeight_lt_dualMinimumDistance
        xCode hminZ hz0 hzlt with
    ⟨x, hx, hnotCommutes⟩
  exact ⟨cssXCheck x, Or.inl ⟨x, hx, rfl⟩, hnotCommutes⟩
end QEC.Coding.PauliSymplectic
