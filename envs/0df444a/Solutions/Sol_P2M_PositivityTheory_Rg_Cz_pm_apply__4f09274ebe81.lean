-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Cz_pm_apply__4f09274ebe81
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:48:21.689715+00:00
-- url     : https://prove2.me/submissions/f8208068-c9e0-4180-a13b-5ef0a4f5f5ff

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
theorem _root_.solution (σ : Equiv.Perm Q) (f : TV n ℂ Q) (I : Q → Fin n) :
    (pm σ : Module.End ℂ (TV n ℂ Q)) f I = f (I ∘ σ) := rfl
end PositivityTheory.Rg.Cz
