-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_integral_k__4854bf227994
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:49:58.300028+00:00
-- url     : https://prove2.me/submissions/c1e7bd7e-0c78-4a7e-951b-a18b4df2ae3a

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_RegMaxReindex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open MeasureTheory
open ReciprocityTheory.AnForm.A (regMax tmax kθ)
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
theorem _root_.solution : ∫ x, kθ x = 1 := by
  unfold kθ
  exact ContDiffBump.integral_normed _
end GroundTheory.Heights₂.Heights.Regular
