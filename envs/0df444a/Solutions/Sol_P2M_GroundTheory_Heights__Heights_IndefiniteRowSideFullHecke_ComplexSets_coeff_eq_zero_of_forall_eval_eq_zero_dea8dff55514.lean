-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_coeff_eq_zero_of_forall_eval_eq_zero_dea8dff55514
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:31:44.188516+00:00
-- url     : https://prove2.me/submissions/6fa95261-8751-4292-bb61-83f50dcf496c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeierstrassPolynomialDivision
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CoeffEqZeroOfForallEvalEqZero

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
open Topology Filter
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {N : ℕ} (e : Fin N → ℂ)
    (he : ∀ t : ℂ, ∑ i : Fin N, e i * t ^ (i : ℕ) = 0) (i : Fin N) : e i = 0 := by
  classical
  have hp : (∑ j : Fin N, Polynomial.C (e j) * Polynomial.X ^ (j : ℕ)) = 0 :=
    Polynomial.funext fun t => by simpa [Polynomial.eval_finsetSum] using he t
  have := congrArg (fun p => Polynomial.coeff p i) hp
  simpa [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Fin.val_inj] using this
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
