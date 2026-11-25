-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormalModelFibre_fibre_finite_4005ccaacd62
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:38:04.412334+00:00
-- url     : https://prove2.me/submissions/2958a20e-f2fb-4925-ac1f-93c36f3145ac

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelProper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PModelLocalizationMaximalPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_NormalModelFibreNear
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isRoot_map_eval_of_mem_zeroSetIn_9b21e58aa6cf


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
open MvPolynomial Filter Topology ComplexSets Metric
noncomputable section
open GroundTheory.Heights₂.Heights.NormalModelFibre
variable {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
namespace GroundTheory.Heights₂.Heights.NormalModelFibre
theorem _root_.solution (q : Fin n → ℂ) :
    {w | w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∧ IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q}.Finite := by
  choose P hPm hP using M.integral
  have hroots : (Set.univ.pi fun i : Fin M.m => {a : ℂ | ((P i).map (eval q)).IsRoot a}).Finite :=
    Set.Finite.pi fun i => Polynomial.finite_setOfPred_isRoot ((hPm i).map _).ne_zero
  refine (hroots.image fun y : Fin M.m → ℂ => Sum.elim q y).subset ?_
  rintro w ⟨hw, rfl⟩
  refine ⟨fun i => w (Sum.inr i), fun i _ => ?_, ?_⟩
  · exact IndefiniteRowSideFullHecke.ComplexSets.isRoot_map_eval_of_mem_zeroSetIn hw i (P i) (hP i)
  · funext s
    rcases s with i | i <;> rfl
end GroundTheory.Heights₂.Heights.NormalModelFibre
