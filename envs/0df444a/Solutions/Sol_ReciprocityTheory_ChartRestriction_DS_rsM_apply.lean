-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.rsM_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:24:58.377907+00:00
-- url     : https://prove2.me/submissions/bc76ff78-6ea6-468d-87b7-ff3627605a6a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_InhabRep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (v : (⊤ : Submodule ℂ (EH n))) :
    ((rsM A v : (⊤ : Submodule ℂ (EH n))) : EH n) = toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A v := rfl
end ReciprocityTheory.ChartRestriction.DS
