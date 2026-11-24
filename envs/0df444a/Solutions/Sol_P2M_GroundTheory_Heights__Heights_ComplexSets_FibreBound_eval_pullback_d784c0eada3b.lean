-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_eval_pullback_d784c0eada3b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:00.608187+00:00
-- url     : https://prove2.me/submissions/a4385005-a568-4431-bf44-3b7169fb4fc9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
variable {n d : ℕ}
open GroundTheory.Heights₂.Heights.ComplexSets.FibreBound
namespace GroundTheory.Heights₂.Heights.ComplexSets.FibreBound
theorem _root_.solution (A : Matrix (Fin d) (Fin n) ℂ) (x : Fin n → ℂ) (P : MvPolynomial (Fin d) ℂ) :
    eval x (pullback A P) = eval (A.mulVec x) P := by
  have h : (eval x).comp (pullback A).toRingHom = eval (A.mulVec x) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [pullback]
    · intro i; simp [pullback, linPoly, Matrix.mulVec, dotProduct]
  exact congrArg (fun f : MvPolynomial (Fin d) ℂ →+* ℂ => f P) h
end GroundTheory.Heights₂.Heights.ComplexSets.FibreBound
