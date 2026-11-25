-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_finitePlace_sum_le_d7c4c106976e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:32:00.662785+00:00
-- url     : https://prove2.me/submissions/9a5b5ab1-bf43-43e6-a325-295478829569

import Theorems.Thm_P2M_UpperTheory_Reformulated_B_FinitePlaceSumBound_finitePlace_sum_le__f64df29d0620
import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterLe
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FinitePlaceSumLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCenterLe

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
open ReciprocityTheory.ChartRestriction.G NumberField MvPolynomial
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {K : Type*} [Field K] [NumberField K] (v : FinitePlace K) {α : Type*}
    (s : Finset α) (f : α → K) {B : ℝ} (hB : 0 ≤ B) (h : ∀ a ∈ s, v (f a) ≤ B) :
    v (∑ a ∈ s, f a) ≤ B :=
  _root_.P2M_UpperTheory_Reformulated_B_FinitePlaceSumBound_finitePlace_sum_le__f64df29d0620 v s f hB h
end GroundTheory.Heights₂.Heights
