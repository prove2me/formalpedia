-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_hk_of_le_64a107755ae3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:49.98183+00:00
-- url     : https://prove2.me/submissions/4d683905-458a-43cc-90b4-749875864151

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongAnnulus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_hk_one_b52240beee02
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_radialTransform_eq_zero_of_const_e9745533580f


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
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.RegLelongAnnulus
namespace GroundTheory.Heights₂.Heights.RegLelongAnnulus
theorem _root_.solution (e k : ℕ) {v : ℝ} (h0 : 0 ≤ v) (hv : v ≤ pk k) :
    radialTransform (e + 1) (hk k) v = 0 :=
  radialTransform_eq_zero_of_const e (hk k) (t₀ := pk k)
    (fun τ hτ => by rw [hk_one hτ.1 hτ.2, hk_one le_rfl (pk_pos k).le]) ⟨h0, hv⟩
end GroundTheory.Heights₂.Heights.RegLelongAnnulus
