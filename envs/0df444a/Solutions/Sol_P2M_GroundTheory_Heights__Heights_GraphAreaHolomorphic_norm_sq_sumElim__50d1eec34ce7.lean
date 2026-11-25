-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_norm_sq_sumElim__50d1eec34ce7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:54:31.116942+00:00
-- url     : https://prove2.me/submissions/23dd61bc-fd29-4daa-90e3-759bca33d90f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaMultiplicity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGraphAreaHolomorphic
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGraphAreaHolomorphic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_norm_sq_sumElim_309aed0fc72d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Module
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.GraphAreaHolomorphic
namespace GroundTheory.Heights₂.Heights.GraphAreaHolomorphic
theorem _root_.solution {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : EuclideanSpace 𝕜 ι) (b : EuclideanSpace 𝕜 κ) :
    ‖(WithLp.toLp 2 (Sum.elim (fun i => a i) (fun i => b i)) : EuclideanSpace 𝕜 (ι ⊕ κ))‖ ^ 2 =
      ‖a‖ ^ 2 + ‖b‖ ^ 2 :=
  norm_sq_sumElim (Equiv.refl _) a b
end GroundTheory.Heights₂.Heights.GraphAreaHolomorphic
