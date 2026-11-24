-- Prove2me | solution 1 for UpperTheory.HF.Formalism.HC.HostRaw.imgOne_eq_bot_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:10:02.210829+00:00
-- url     : https://prove2.me/submissions/b6085342-97af-462e-8089-16cc66f64f8a

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
theorem _root_.solution {f : ℕ} (hf : f ∣ H.condN) :
    H.imgOne f = ⊥ ↔ ∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD f] → H.art u = 1 := by
  rw [Subgroup.eq_bot_iff_forall]
  constructor
  · intro h u hu; exact h _ ((H.mem_imgOne hf _).2 ⟨u, hu, rfl⟩)
  · intro h g hg; obtain ⟨u, hu, rfl⟩ := (H.mem_imgOne hf _).1 hg; exact h u hu
end UpperTheory.HF.Formalism.HC.HostRaw
