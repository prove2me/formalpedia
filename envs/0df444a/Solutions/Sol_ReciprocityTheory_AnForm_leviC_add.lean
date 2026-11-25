-- Prove2me | solution 1 for ReciprocityTheory.AnForm.leviC_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:08:53.54032+00:00
-- url     : https://prove2.me/submissions/810f6bb2-4968-42fd-9bf9-2bfe799f1195

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
theorem _root_.solution {e : ℕ} (H : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) →L[ℝ] ℝ) (a a' b : Fin e → ℂ) :
    leviC H (a + a') b = leviC H a b + leviC H a' b := by
  unfold leviC
  simp only [smul_add, map_add, ContinuousLinearMap.add_apply]
  push_cast
  ring
end ReciprocityTheory.AnForm
