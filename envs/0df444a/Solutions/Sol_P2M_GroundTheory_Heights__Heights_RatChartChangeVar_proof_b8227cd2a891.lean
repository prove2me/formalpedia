-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RatChartChangeVar_proof_b8227cd2a891
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:20:04.212265+00:00
-- url     : https://prove2.me/submissions/4e6d0d9c-2929-4345-b6ec-eabdab8640e8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatChartChangeVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetNoChartNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartSheetNoRatNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIntegralIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPosPartSplit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PRatChartChangeVar
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatChartChangeVar_ratInt_eq_posParts_a563026af33a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatChartChangeVar_posPart_eq_457a933ba476
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IntegralIndep_chartInt_eq_posParts_786379f5608c
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
namespace GroundTheory.Heights₂.Heights
namespace RatChartChangeVar
theorem _root_.solution (hM : RatSheetSumMeasurable.Statement) (hN1 : RatSheetNoChartNull.Statement)
    (hN2 : ChartSheetNoRatNull.Statement) (hL : RatPosPartLocal.Statement) :
    RatChartChangeVar.Statement := by
  intro n d J A p q f φ hJ hd hA hq hfin hf hφ
  have m1 : Measurable (RatChart.ratDens J p q f φ) :=
    hM n d J p q (fun a b => a * b) f φ hfin (continuous_fst.mul continuous_snd).measurable hf
  have m2 : Measurable (RatChart.ratAbsDens J p q f φ) :=
    hM n d J p q (fun a b => |a * b|) f φ hfin (continuous_fst.mul continuous_snd).abs.measurable hf
  refine ⟨m1.aestronglyMeasurable, m2.aestronglyMeasurable, fun hi => ?_⟩
  have e0 := RatChartChangeVar.posPart_eq hM hN1 hN2 hL hJ hd hA hq hfin hf hφ
  have e1 := RatChartChangeVar.posPart_eq hM hN1 hN2 hL hJ hd hA hq hfin hf.neg hφ
  obtain ⟨iR, cR⟩ := RatChartChangeVar.ratInt_eq_posParts hM hfin hf φ
  obtain ⟨iA, cA⟩ := IntegralIndep.chartInt_eq_posParts hA hf φ
  have hi' : Integrable (chartAbsDens J A f φ) := iA.2 (by rw [← e0, ← e1]; exact iR.1 hi)
  exact ⟨hi', by rw [cR hi, cA hi', e0, e1]⟩
end RatChartChangeVar
end GroundTheory.Heights₂.Heights
