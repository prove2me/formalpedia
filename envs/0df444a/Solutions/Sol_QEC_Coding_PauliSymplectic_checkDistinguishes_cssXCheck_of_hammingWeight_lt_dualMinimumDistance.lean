-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.checkDistinguishes_cssXCheck_of_hammingWeight_lt_dualMinimumDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:27:12.033294+00:00
-- url     : https://prove2.me/submissions/49308ea6-3e35-4cb1-bf44-1bfa40050c99

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
open QEC.Coding.PauliSymplectic
variable {ι : Type u} [Fintype ι]
variable [DecidableEq ι]
omit [DecidableEq ι]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution
    (xCode zCode : LinearCode (ZMod 2) ι) {dX : Nat}
    (hminX : MinimumDistance zCode.dual dX)
    {x : Word (ZMod 2) ι} (hx0 : x ≠ 0) (hxlt : HammingWeight x < dX) :
    checkDistinguishes (binaryCSSCheckSet xCode zCode) (cssXCheck x) := by
  rcases
      exists_z_check_not_commutes_cssXCheck_of_hammingWeight_lt_dualMinimumDistance
        zCode hminX hx0 hxlt with
    ⟨z, hz, hnotCommutes⟩
  exact ⟨cssZCheck z, Or.inr ⟨z, hz, rfl⟩, hnotCommutes⟩
end QEC.Coding.PauliSymplectic
