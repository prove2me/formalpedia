-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_integrable_chartDens_daacb8db24dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:17:05.500142+00:00
-- url     : https://prove2.me/submissions/659c17d5-8f9b-48e5-ab40-b2202c90c4b1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongRegularise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffDominated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_SliceCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceFormLelongCompactLimit
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
open scoped ContDiff Manifold
noncomputable section
open GroundTheory.Heights₂.Heights.SliceFormLelongCompact
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.SliceFormLelongCompact
theorem _root_.solution {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hA : IsFiniteProjection J A) {w : (Fin n → ℂ) → ℝ} {ψ : Fin d → (Fin n → ℂ) → ℝ}
    (hm : Measurable (chartDens J A w ψ)) (hi : Integrable (chartAbsDens J A w ψ)) :
    Integrable (chartDens J A w ψ) := by
  refine hi.mono' hm.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y
  rw [Real.norm_eq_abs]
  unfold chartDens chartAbsDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  split_ifs <;> simp
end GroundTheory.Heights₂.Heights.SliceFormLelongCompact
