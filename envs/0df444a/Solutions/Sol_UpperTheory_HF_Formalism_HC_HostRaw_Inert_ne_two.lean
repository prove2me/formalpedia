-- Prove2me | solution 1 for UpperTheory.HF.Formalism.HC.HostRaw.Inert.ne_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:58:11.070823+00:00
-- url     : https://prove2.me/submissions/e6c9ada1-16aa-4379-b68c-9b87502744cb

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_PrimePairSizeCondition
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_SizeDefs
import Theorems.Thm_Formalism_HC_HostRaw_d_mod_eight


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
theorem _root_.solution {H : HostRaw φ} {p : ℕ} (h : H.Inert p) : p ≠ 2 := by
  rintro rfl
  have h1 := h.2
  have h8 := H.d_mod_eight
  have h2 : jacobiSym (-(H.d : ℤ)) 2 = jacobiSym 1 2 := by
    apply jacobiSym.mod_left'
    push_cast
    omega
  rw [h2, jacobiSym.one_left] at h1
  exact absurd h1 (by decide)
end Inert
end UpperTheory.HF.Formalism.HC.HostRaw
