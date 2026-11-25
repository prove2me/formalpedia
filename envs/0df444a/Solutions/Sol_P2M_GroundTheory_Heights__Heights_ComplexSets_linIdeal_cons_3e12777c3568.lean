-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_linIdeal_cons_3e12777c3568
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:51:57.318621+00:00
-- url     : https://prove2.me/submissions/1afa629c-6b0a-4498-a7bf-e178e08b0e20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeAvoidsExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLinearFormCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHomogDimZeroPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsExists

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
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution {k : ℕ} (A : Matrix (Fin k) (Fin n) ℂ) (B : Matrix (Fin 1) (Fin n) ℂ) :
    linIdeal (Matrix.of (Fin.cons (B 0) A : Fin (k + 1) → Fin n → ℂ)) = linIdeal A ⊔ linIdeal B := by
  have h : linPoly (Matrix.of (Fin.cons (B 0) A : Fin (k + 1) → Fin n → ℂ)) =
      Fin.cons (linPoly B 0) (linPoly A) := by
    funext i
    exact Fin.cases rfl (fun i => rfl) i
  have hB : Set.range (linPoly B) = {linPoly B 0} := by
    rw [Set.range_unique]
    rfl
  rw [linIdeal, linIdeal, linIdeal, h, Fin.range_cons, hB, Set.insert_eq, Ideal.span_union, sup_comm]
end GroundTheory.Heights₂.Heights.ComplexSets
