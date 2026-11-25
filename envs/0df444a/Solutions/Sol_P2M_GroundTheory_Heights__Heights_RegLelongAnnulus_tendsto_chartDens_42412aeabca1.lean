-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_tendsto_chartDens_42412aeabca1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:48:48.456545+00:00
-- url     : https://prove2.me/submissions/d1d963ee-d791-4e67-90d8-4aa8052aee5f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongAnnulus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionCluster_fibre_finite_7d46f66826ee
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_fibre_finite_20785c71949c


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
variable {n m : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin m) (Fin n) ℂ}
namespace GroundTheory.Heights₂.Heights.RegLelongAnnulus
theorem _root_.solution (hA : IsFiniteProjection J A) {w : ℕ → (Fin n → ℂ) → ℝ} {w' : (Fin n → ℂ) → ℝ}
    (hw : ∀ z, Tendsto (fun k => w k z) atTop (𝓝 (w' z))) (φ : Fin m → (Fin n → ℂ) → ℝ) (y : Fin m → ℂ) :
    Tendsto (fun k => chartDens J A (w k) φ y) atTop (𝓝 (chartDens J A w' φ y)) := by
  have hfin : (fibre J A y).Finite := FiniteProjectionCluster.fibre_finite J A hA y
  unfold chartDens sheetSum
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine tendsto_finsetSum _ fun z _ => ?_
  split_ifs with h
  · exact (hw z).mul_const _
  · exact tendsto_const_nhds
end GroundTheory.Heights₂.Heights.RegLelongAnnulus
