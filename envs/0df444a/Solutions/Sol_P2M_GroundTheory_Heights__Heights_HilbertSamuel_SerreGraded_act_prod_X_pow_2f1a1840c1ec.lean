-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_act_prod_X_pow_2f1a1840c1ec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:31.397554+00:00
-- url     : https://prove2.me/submissions/421335c6-f342-496a-9a7a-e6e786f0d702

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSerreGraded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PSerreGraded
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_act_X_5d3e9f420ff7

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
theorem _root_.solution (μ : Fin q → ℕ) :
    act w (∏ j, MvPolynomial.X j ^ μ j) = C (∏ j, w j ^ μ j) * X ^ (∑ j, μ j) := by
  simp [map_prod, act_X, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
end GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
