-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_embForm_ne_C_ab4f1ef91293
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:23:18.651801+00:00
-- url     : https://prove2.me/submissions/c5f51a03-4b9b-48d4-acae-38548f5d1a2c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormFormIrreducible
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_eval_embForm_a7d551bb504e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_eval_embForm_alt_f3240423aa8e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial TensorProduct Matrix
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial
open GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
variable {E L K : Type*} [Field E] [Field L] [Field K] [Algebra E L] [Algebra E K] {n : ℕ}
  {x : Fin n → L} {t : Fin n → E}
namespace GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
theorem _root_.solution (σ : L →ₐ[E] K) (ht : ∑ j, algebraMap E L (t j) * x j = 1) (r : K) :
    embForm σ x ≠ C r := by
  intro h
  have h1 := congrArg (eval fun j => algebraMap E K (t j)) h
  rw [eval_embForm_alt σ ht, eval_C] at h1
  have h0 : r = 0 := by
    have h0 := congrArg (eval 0) h
    rw [eval_embForm, eval_C] at h0
    simpa using h0.symm
  exact one_ne_zero (h1.trans h0)
end GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
