-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.pm_pm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:41:59.318162+00:00
-- url     : https://prove2.me/submissions/5f32559a-bf65-4b3a-aca0-f99dd681d0c1

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_KTypeData
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CasimirBounds_ReSwapSumLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
variable {n : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]
namespace PositivityTheory.Rg.Cz
theorem _root_.solution (σ τ : Equiv.Perm Q) (f : TV n ℂ Q) :
    (pm σ : Module.End ℂ (TV n ℂ Q)) (pm τ f) = pm (σ * τ) f := rfl
end PositivityTheory.Rg.Cz
