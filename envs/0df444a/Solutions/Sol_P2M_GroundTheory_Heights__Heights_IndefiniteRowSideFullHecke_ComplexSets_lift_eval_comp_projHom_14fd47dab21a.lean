-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_lift_eval_comp_projHom_14fd47dab21a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:32.003132+00:00
-- url     : https://prove2.me/submissions/0c8823b8-29dd-4ace-a7a3-e96949ea4bf0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GraphChartEventuallyEqSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsSheetMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LogIntegrableOnOfLogIntegrable

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
open MvPolynomial MeasureTheory Filter
noncomputable section
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    {x : Fin n → ℂ} (hx : x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J) :
    (Ideal.Quotient.lift J (MvPolynomial.eval x) fun q hq => hx q hq).comp
        (GroundTheory.Heights₂.Heights.ComplexSets.projHom J A).toRingHom =
      MvPolynomial.eval (A.mulVec x) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [GroundTheory.Heights₂.Heights.ComplexSets.projHom, GroundTheory.Heights₂.Heights.ComplexSets.pullback]
  · intro i
    simp [GroundTheory.Heights₂.Heights.ComplexSets.projHom, GroundTheory.Heights₂.Heights.ComplexSets.pullback,
      GroundTheory.Heights₂.Heights.ComplexSets.linPoly, Matrix.mulVec, dotProduct]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
