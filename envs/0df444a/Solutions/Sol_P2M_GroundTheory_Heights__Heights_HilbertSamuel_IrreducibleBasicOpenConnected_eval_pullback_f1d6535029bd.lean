-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleBasicOpenConnected_eval_pullback_f1d6535029bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:54.339937+00:00
-- url     : https://prove2.me/submissions/abd891b9-326e-4c5d-9b41-40116a7ac242

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_BasicOpenSteps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial Filter Topology
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace IrreducibleBasicOpenConnected
theorem _root_.solution {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ)
    (P : MvPolynomial (Fin d) ℂ) (x : Fin n → ℂ) :
    eval x (ComplexSets.pullback A P) = eval (A.mulVec x) P := by
  have h : ∀ i, eval x (ComplexSets.linPoly A i) = A.mulVec x i := by
    intro i
    simp [ComplexSets.linPoly, Matrix.mulVec, dotProduct, map_sum]
  rw [ComplexSets.pullback, aeval_eq_bind₁]
  change eval₂Hom (RingHom.id ℂ) x (bind₁ (ComplexSets.linPoly A) P) =
    eval₂Hom (RingHom.id ℂ) (A.mulVec x) P
  rw [eval₂Hom_bind₁]
  congr 2
  funext i
  exact h i
end IrreducibleBasicOpenConnected
end GroundTheory.Heights₂.Heights.HilbertSamuel
