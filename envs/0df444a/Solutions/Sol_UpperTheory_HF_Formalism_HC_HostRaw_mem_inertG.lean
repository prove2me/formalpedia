-- Prove2me | solution 1 for UpperTheory.HF.Formalism.HC.HostRaw.mem_inertG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:07:18.707635+00:00
-- url     : https://prove2.me/submissions/cb108897-6295-46f6-91a3-cb7a140dcb14

import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_SlopeTestRemainingChoices
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Theorems.Thm_UpperTheory_HF_Formalism_HC_HostRaw_mem_imgOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open UpperTheory UpperTheory.HF UpperTheory.HF.Formalism UpperTheory.HF.Formalism.HC UpperTheory.HF.Formalism.HC.HostRaw
open UpperTheory.HF _root_.Formalism _root_.Formalism.HC _root_.Formalism.HC.HostRaw
variable {φ : Frame} (H : HostRaw φ)
namespace UpperTheory.HF.Formalism.HC.HostRaw
theorem _root_.solution (l : ℕ) (g : φ.GG) :
    g ∈ H.inertG l ↔ ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD ordCompl[l] H.condN] ∧ g = H.art u :=
  H.mem_imgOne (Nat.ordCompl_dvd _ _) g
end UpperTheory.HF.Formalism.HC.HostRaw
