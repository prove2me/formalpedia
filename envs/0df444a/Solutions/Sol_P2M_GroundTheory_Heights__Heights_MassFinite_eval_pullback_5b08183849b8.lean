-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MassFinite_eval_pullback_5b08183849b8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:57.678577+00:00
-- url     : https://prove2.me/submissions/8392e6d6-f0c7-4db8-8bdc-fcf3efa2e1ee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalGraphMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMassFinite

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
open MvPolynomial MeasureTheory Matrix
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.MassFinite
namespace GroundTheory.Heights₂.Heights.MassFinite
theorem _root_.solution {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) (P : MvPolynomial (Fin d) ℂ)
    (x : Fin n → ℂ) : eval x (ComplexSets.pullback A P) = eval (A *ᵥ x) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [ComplexSets.pullback]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, hp]
    simp [ComplexSets.pullback, ComplexSets.linPoly, Matrix.mulVec, dotProduct]
end GroundTheory.Heights₂.Heights.MassFinite
