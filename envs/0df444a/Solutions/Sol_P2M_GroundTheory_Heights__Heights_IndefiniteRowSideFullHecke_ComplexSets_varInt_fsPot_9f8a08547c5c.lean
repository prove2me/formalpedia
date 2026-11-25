-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_varInt_fsPot_9f8a08547c5c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:43:07.686276+00:00
-- url     : https://prove2.me/submissions/56aa66de-2b15-4d7f-99b0-9577600db913

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GraphChartEventuallyEqSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PlaneIdealTwoOne
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_maDens_const_smul_b1911d85dc13

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial MeasureTheory
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {n : ℕ} (h : GroundTheory.Heights₂.Heights.HermNorm n)
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (f : (Fin n → ℂ) → ℝ) :
    GroundTheory.Heights₂.Heights.varInt J 1 f (fun _ => fsPot h) =
      2 * GroundTheory.Heights₂.Heights.varInt J 1 f (fun _ y => Real.log (h.dualNorm y)) := by
  unfold GroundTheory.Heights₂.Heights.varInt
  split_ifs with hA
  · unfold GroundTheory.Heights₂.Heights.chartInt
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [GroundTheory.Heights₂.Heights.chartDens, GroundTheory.Heights₂.Heights.sheetSum]
    rw [mul_finsum_mem]
    refine finsum_mem_congr rfl fun x _ => ?_
    split_ifs with hs
    · have hc : (fun k : Fin 1 => (fun _ : Fin 1 => fsPot h) k ∘ hs.choose) =
          fun k : Fin 1 => (2 : ℝ) • ((fun _ : Fin 1 => fun y => Real.log (h.dualNorm y)) k ∘ hs.choose) := by
        funext k w
        simp [fsPot, Real.log_pow]
      rw [hc, maDens_const_smul]
      ring
    · simp
  · simp
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
