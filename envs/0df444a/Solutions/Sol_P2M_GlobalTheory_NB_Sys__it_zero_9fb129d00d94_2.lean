-- Prove2me | solution 2 for P2M_GlobalTheory_NB_Sys__it_zero_9fb129d00d94
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:52:28.021015+00:00
-- url     : https://prove2.me/submissions/a6b41f25-d4a7-45ab-93d7-3cdf7027a18f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MapCSmulMulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open GlobalTheory GlobalTheory.NB
attribute [instance] Fr.eeRing Fr.eeAlgA Fr.eeAlgO Fr.eeTow
open GlobalTheory.NB.Sys
variable {l : ℕ} {O : Type} [CommRing O] {R : Fr l O} {n r : ℕ} (S : Sys R n r)
namespace GlobalTheory.NB.Sys
theorem _root_.solution (c : ZMod n) : S.φit c 0 = LinearMap.id := rfl
end GlobalTheory.NB.Sys
