-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.prodAtlas_holoMap_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:44:47.758878+00:00
-- url     : https://prove2.me/submissions/05ee024d-2d5c-4298-b022-e4266aca5a2d

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HomogeneousLiftHolomorphicOnSnd
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_FubiniStudyPotentialProductIsPotential
import Theorems.Thm_ReciprocityTheory_AnForm_M_prodChart_holo_snd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint CompatibleChartOperations
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {e e' : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) : HoloMap (prodAtlas A B) B Prod.snd :=
  ⟨continuous_snd, fun _ l => prodChart_holo_snd A B _ _ l⟩
end ReciprocityTheory.AnForm.M
