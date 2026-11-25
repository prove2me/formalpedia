-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_hasFDerivAt_cofactorFn_a81428026681
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:29:50.146425+00:00
-- url     : https://prove2.me/submissions/2cb62286-9629-4a34-8c13-5e6d7ef006fd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChangeOfVariablesDegreePiola
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_update_eq_killRow_086bc23a53e7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open scoped ContDiff
open MeasureTheory
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ChangeOfVariablesDegree
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ChangeOfVariablesDegree
theorem _root_.solution (H : (Fin n → ℝ) → Fin n → ℝ) (hH : ContDiff ℝ ∞ H)
    (i j : Fin n) (x : Fin n → ℝ) :
    HasFDerivAt (cofactorFn H i j)
      ((detCML.linearDeriv (Function.update (jacobian H x) i (Pi.single j 1))).comp
        ((killRow i).comp (entriesCLM.comp (fderiv ℝ (fderiv ℝ H) x)))) x := by
  have h2 : HasFDerivAt (fderiv ℝ H) (fderiv ℝ (fderiv ℝ H) x) x :=
    ((hH.fderiv_right (m := ∞) le_rfl).differentiable (by simp)).differentiableAt.hasFDerivAt
  have hM : HasFDerivAt
      (fun y => (Function.update (jacobian H y) i (Pi.single j 1) : Fin n → Fin n → ℝ))
      ((killRow i).comp (entriesCLM.comp (fderiv ℝ (fderiv ℝ H) x))) x := by
    have : (fun y => (Function.update (jacobian H y) i (Pi.single j 1) : Fin n → Fin n → ℝ)) =
        fun y => killRow i (entriesCLM (fderiv ℝ H y)) + Pi.single i (Pi.single j 1) := by
      funext y; exact update_eq_killRow _ _ _
    rw [this]
    exact ((killRow i).hasFDerivAt.comp x (entriesCLM.hasFDerivAt.comp x h2)).add_const _
  exact (detCML.hasFDerivAt _).comp x hM
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ChangeOfVariablesDegree
