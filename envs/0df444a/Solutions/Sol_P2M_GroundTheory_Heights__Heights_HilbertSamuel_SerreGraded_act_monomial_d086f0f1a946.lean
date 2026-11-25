-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_act_monomial_d086f0f1a946
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:28.734354+00:00
-- url     : https://prove2.me/submissions/50e9155e-9e6b-431a-88ac-e14c66ce0da4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSerreGraded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PSerreGraded

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
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
open Polynomial
variable {Ω : Type} [Field Ω] {q : ℕ} (w : Fin q → Ω)
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
theorem _root_.solution (v : Fin q →₀ ℕ) (a : ℤ) :
    act w (MvPolynomial.monomial v a) = C ((a : Ω) * ∏ j, w j ^ v j) * X ^ (∑ j, v j) := by
  rw [act, MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, mul_assoc]
end GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
