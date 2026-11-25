-- Prove2me | solution 1 for UpperTheory.HF.Formalism.HC.HostRaw.Inert.not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:22:31.277875+00:00
-- url     : https://prove2.me/submissions/ee20045a-3566-4906-8d36-7eb36e2c45a2

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_PrimePairSizeCondition
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_SizeDefs
import Theorems.Thm_UpperTheory_HF_Formalism_HC_HostRaw_Inert_ne_two
import Theorems.Thm_Formalism_HC_HostRaw_not_dvd_condN_of_inert


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open UpperTheory UpperTheory.HF UpperTheory.HF.Formalism UpperTheory.HF.Formalism.HC
open UpperTheory.HF _root_.Formalism _root_.Formalism.HC
open UpperTheory.HF.Formalism.HC.HostRaw
open _root_.Formalism.HC.HostRaw
variable {φ : Frame} (H : HostRaw φ)
namespace UpperTheory.HF.Formalism.HC.HostRaw
namespace Inert
theorem _root_.solution {H : HostRaw φ} {p : ℕ} (h : H.Inert p) : ¬ p ∣ H.condN :=
  H.not_dvd_condN_of_inert h.1 h.ne_two h.2
end Inert
end UpperTheory.HF.Formalism.HC.HostRaw
