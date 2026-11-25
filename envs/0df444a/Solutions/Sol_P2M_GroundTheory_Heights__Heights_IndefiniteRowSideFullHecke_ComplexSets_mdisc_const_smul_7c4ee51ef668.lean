-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mdisc_const_smul_7c4ee51ef668
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:28:19.264492+00:00
-- url     : https://prove2.me/submissions/66774c55-a626-4390-b17c-6edd470cbaba

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GraphChartEventuallyEqSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PlaneIdealTwoOne

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
theorem _root_.solution {D : ℕ} (c : ℂ) (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    ReciprocityTheory.AnForm.mdisc (fun k => c • A k) = c ^ D * ReciprocityTheory.AnForm.mdisc A := by
  unfold ReciprocityTheory.AnForm.mdisc
  simp only [← Finset.smul_sum, Matrix.det_smul, Fintype.card_fin, Finset.mul_sum]
  exact Finset.sum_congr rfl fun S _ => by ring
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
