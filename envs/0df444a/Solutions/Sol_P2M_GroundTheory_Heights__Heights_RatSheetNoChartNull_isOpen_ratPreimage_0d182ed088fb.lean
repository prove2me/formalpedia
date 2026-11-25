-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RatSheetNoChartNull_isOpen_ratPreimage_0d182ed088fb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:28:47.008389+00:00
-- url     : https://prove2.me/submissions/c62175fa-c692-4404-8000-7f1cc1af9333

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetNoChartNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetOnlyNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCriticalImageNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PRatSheetNoChartNull
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatSheetNoChartNull_continuousOn_ratMap_aee27c8cf252

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.RatSheetNoChartNull
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.RatSheetNoChartNull
theorem _root_.solution (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ)
    {S : Set (Fin d → ℂ)} (hS : IsOpen S) :
    IsOpen ({x | eval x q ≠ 0} ∩ RatChart.ratMap p q ⁻¹' S) :=
  (continuousOn_ratMap p q).isOpen_inter_preimage
    (isOpen_ne_fun (MvPolynomial.continuous_eval q) continuous_const) hS
end GroundTheory.Heights₂.Heights.RatSheetNoChartNull
