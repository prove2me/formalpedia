-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.tE_zero_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:37:56.50566+00:00
-- url     : https://prove2.me/submissions/59f8f8b3-5326-4b37-a65a-8c1f054423cc

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CasimirBounds_ReSwapSumLe
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CasimirBounds_Expand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
variable {n : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]
namespace PositivityTheory.Rg.Cz
theorem _root_.solution (S : Finset Q) (a c : Fin n) (f : TV n ℂ Q) (I : Q → Fin n) :
    (tE S (0 : Fin n → Fin n → Module.End ℂ ℂ) a c : Module.End ℂ (TV n ℂ Q)) f I =
      ∑ p ∈ S, (eAt p a c : Module.End ℂ (TV n ℂ Q)) f I := by
  simp [tE, lift, LinearMap.add_apply, LinearMap.sum_apply, Finset.sum_apply]
end PositivityTheory.Rg.Cz
