-- Prove2me | solution 1 for UpperTheory.HF.Formalism.HC.HostRaw.imgOne_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:07:18.511639+00:00
-- url     : https://prove2.me/submissions/b97004d4-fe9b-4ea0-8a7b-4a6ae0bc9584

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
theorem _root_.solution {f g : ℕ} (hfg : f ∣ g) (hg : g ∣ H.condN) : H.imgOne g ≤ H.imgOne f := fun x hx => by
  obtain ⟨u, hu, rfl⟩ := (H.mem_imgOne hg _).1 hx
  exact (H.mem_imgOne (hfg.trans hg) _).2 ⟨u, hu.of_dvd hfg, rfl⟩
end UpperTheory.HF.Formalism.HC.HostRaw
