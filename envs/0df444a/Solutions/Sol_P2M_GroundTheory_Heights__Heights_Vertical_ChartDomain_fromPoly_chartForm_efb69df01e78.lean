-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_chartForm_efb69df01e78
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:22:42.413718+00:00
-- url     : https://prove2.me/submissions/3e33414a-4d09-4668-8376-fd42eb13958b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartDomain
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_cx_85517b06cadd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_X_2b090bd40426

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.ChartDomain
variable {D : Type} [CommRing D] {n e : ℕ} (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n)
namespace GroundTheory.Heights₂.Heights.Vertical.ChartDomain
theorem _root_.solution :
    fromPoly Q j e (∑ m, X (.inr m) * cx Q j e m - 1) = 0 := by
  have hmem : chartForm (X : Par e n → MvPolynomial (Par e n) D) - 1 ∈ secI Q e :=
    Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  rw [← toChart_eq_zero Q j hmem]
  simp only [map_sum, map_mul, map_sub, map_one, fromPoly_X, fromPoly_cx, chartForm, linForm]
end GroundTheory.Heights₂.Heights.Vertical.ChartDomain
