-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.stabilizerSyndromeBit_eq_one_iff_not_commutes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:22:21.044512+00:00
-- url     : https://prove2.me/submissions/c4ecadd4-24d4-4fc3-be67-317cd0715215

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerSyndromeBit_eq_zero_iff_commutes

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
theorem _root_.solution (M E : Binary ι) :
    stabilizerSyndromeBit M E = 1 ↔ ¬ Commutes E M := by
  constructor
  · intro hOne hCommutes
    have hZero := (stabilizerSyndromeBit_eq_zero_iff_commutes M E).2 hCommutes
    rw [hZero] at hOne
    exact zero_ne_one hOne
  · intro hNotCommutes
    apply zmod_two_eq_one_of_ne_zero
    intro hZero
    exact hNotCommutes ((stabilizerSyndromeBit_eq_zero_iff_commutes M E).1 hZero)
end QEC.Coding.PauliSymplectic
