-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.CompatibleChartOperations.isCompatChart_restrOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:22:35.926398+00:00
-- url     : https://prove2.me/submissions/f1dd4925-3de4-4577-9022-9407ad300db5

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HomogeneousLiftHolomorphicOnSnd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open OnePoint
noncomputable section
open ReciprocityTheory.AnForm.M.CompatibleChartOperations
namespace ReciprocityTheory.AnForm.M.CompatibleChartOperations
theorem _root_.solution {e : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas e X)
    (i : Fin A.n) (s : Set X) (hs : IsOpen s) : IsCompatChart A ((A.chart i).restrOpen s hs) := by
  intro j
  constructor
  · exact (A.holo j i).mono (fun x hx => ⟨hx.1, hx.2.1⟩)
  · exact (A.holo i j).mono (fun x hx => ⟨hx.1.1, hx.2⟩)
end ReciprocityTheory.AnForm.M.CompatibleChartOperations
