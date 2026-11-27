-- Prove2me | solution 1 for UpperTheory.HF.Formalism.HC.HostRaw.Inert.coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:33:57.788535+00:00
-- url     : https://prove2.me/submissions/cbdb36e0-83fe-40d1-a204-7ac63e03eac8

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_PrimePairSizeCondition
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_SizeDefs
import Theorems.Thm_UpperTheory_HF_Formalism_HC_HostRaw_Inert_not_dvd

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
theorem _root_.solution {H : HostRaw φ} {p : ℕ} (h : H.Inert p) : Nat.Coprime p H.condN :=
  h.1.coprime_iff_not_dvd.2 h.not_dvd
end Inert
end UpperTheory.HF.Formalism.HC.HostRaw
