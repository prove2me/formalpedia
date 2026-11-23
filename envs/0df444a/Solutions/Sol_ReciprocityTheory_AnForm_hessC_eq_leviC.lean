-- Prove2me | solution 1 for ReciprocityTheory.AnForm.hessC_eq_leviC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:45.87157+00:00
-- url     : https://prove2.me/submissions/ebb2b021-7366-4087-bd16-912a4ea385b3

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open Complex Filter Topology
open scoped Matrix
noncomputable section
namespace ReciprocityTheory.AnForm
theorem _root_.solution {e : ℕ} (f : (Fin e → ℂ) → ℝ) (z : Fin e → ℂ) (i j : Fin e) :
    hessC f z i j = leviC (fderiv ℝ (fderiv ℝ f) z) (Pi.single i 1) (Pi.single j 1) := rfl
end ReciprocityTheory.AnForm
