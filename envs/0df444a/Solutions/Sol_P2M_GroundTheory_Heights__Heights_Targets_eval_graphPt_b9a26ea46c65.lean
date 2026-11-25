-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_eval_graphPt_b9a26ea46c65
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:22:06.131074+00:00
-- url     : https://prove2.me/submissions/f00cb25b-a5f9-4664-89dd-2852bac03ed0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_GraphIdeal

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet)
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.Targets
theorem _root_.solution (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) (q : MvPolynomial (Fin (n + 1)) ℂ) :
    eval (graphPt p x) q = eval x (graphHom p q) := by
  have h : (eval (graphPt p x) : MvPolynomial (Fin (n + 1)) ℂ →+* ℂ) =
      (eval x).comp (graphHom p).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [graphPt, graphHom]
      · simp [graphPt, graphHom]
  exact congrArg (fun φ : MvPolynomial (Fin (n + 1)) ℂ →+* ℂ => φ q) h
end GroundTheory.Heights₂.Heights.Targets
