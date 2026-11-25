-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiffOn_remR_a4c875064d53
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:45:12.38+00:00
-- url     : https://prove2.me/submissions/3a4e78d9-0b41-4533-8ec0-aa12ec839210

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PXiMetric
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiff_evC_805e54f1fd45
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiff_ynorm_e2aaff3e7ba5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiff_dnorm_1d46eff272bd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
open scoped ComplexOrder
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]
variable {G : YPt ι ν κ → Matrix κ κ ℂ} (hG : IsEEMetric G)
include hG
omit hG
namespace GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness
theorem _root_.solution (N : ℕ) {q : ℕ} (r : Fin q → MRing (T.yyIdx ι ν κ)) (b : Fin q → T.YBlk → ℕ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (remR N r b) (goodY ι ν κ) := by
  unfold remR
  refine (contDiff_ynorm.pow _).contDiffOn.mul (ContDiffOn.sum fun j _ => ?_)
  refine ContDiffOn.div ((contDiff_norm_sq ℝ).comp (contDiff_evC (r j))).contDiffOn
    ((contDiff_ynorm.pow _).mul (contDiff_dnorm.pow _)).contDiffOn fun w hw => ?_
  exact mul_ne_zero (pow_ne_zero _ (ynorm_pos hw).ne') (pow_ne_zero _ (dnorm_pos hw).ne')
end GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness
