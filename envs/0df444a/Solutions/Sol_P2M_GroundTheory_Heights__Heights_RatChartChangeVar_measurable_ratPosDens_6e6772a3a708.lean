-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RatChartChangeVar_measurable_ratPosDens_6e6772a3a708
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:52.761197+00:00
-- url     : https://prove2.me/submissions/27374983-6d8c-4308-9ed5-36520689621b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatChartChangeVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetNoChartNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartSheetNoRatNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIntegralIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPosPartSplit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PRatChartChangeVar
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsDegZeroSmooth_mul_ac2f2d59f4e1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix ComplexSets
open GroundTheory.Heights₂.Heights.RatChartChangeVar
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.RatChartChangeVar
theorem _root_.solution (hM : RatSheetSumMeasurable.Statement) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {p : Fin d → MvPolynomial (Fin n) ℂ} {q : MvPolynomial (Fin n) ℂ}
    (hfin : ∀ y, (RatChart.ratFibre J p q y).Finite) {f : (Fin n → ℂ) → ℝ} (hf : Measurable f)
    (φ : Fin d → (Fin n → ℂ) → ℝ) : Measurable (RatChart.ratPosDens J p q f φ) :=
  hM n d J p q (fun a b => max (a * b) 0) f φ hfin
    ((continuous_fst.mul continuous_snd).max continuous_const).measurable hf
end GroundTheory.Heights₂.Heights.RatChartChangeVar
