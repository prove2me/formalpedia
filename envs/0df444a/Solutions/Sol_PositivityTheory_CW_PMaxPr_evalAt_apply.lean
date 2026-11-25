-- Prove2me | solution 1 for PositivityTheory.CW.PMaxPr.evalAt_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:36:16.506691+00:00
-- url     : https://prove2.me/submissions/90056377-4030-49b0-badf-792c87ba82a6

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_PMaxPr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.PMaxPr
namespace PositivityTheory.CW.PMaxPr
theorem _root_.solution {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (g : Matrix (Fin n) (Fin n) ℂ)
    (F : V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (v : V) : evalAt g F v = F v g := rfl
end PositivityTheory.CW.PMaxPr
