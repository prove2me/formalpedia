-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_eq_of_embForm_dvd_53e4b6a641c5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:51:30.946199+00:00
-- url     : https://prove2.me/submissions/b0a2f6f5-7d9a-468f-a665-48cfce3642ac

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormFormIrreducible
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_eval_embForm_a7d551bb504e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_eval_embForm_alt_f3240423aa8e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_irreducible_embForm_1ef6dfeea45a

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
theorem _root_.solution (hgen : Algebra.adjoin E (Set.range x) = ⊤)
    (ht : ∑ j, algebraMap E L (t j) * x j = 1) {σ τ : L →ₐ[E] K}
    (h : embForm σ x ∣ embForm τ x) : σ = τ := by
  obtain ⟨q, hq⟩ := h
  have hu : IsUnit q := ((irreducible_embForm τ ht).isUnit_or_isUnit hq).resolve_left
    (irreducible_embForm σ ht).not_isUnit
  obtain ⟨r, -, rfl⟩ := isUnit_iff_eq_C_of_isReduced.mp hu
  have hr : r = 1 := by
    have := congrArg (eval fun j => algebraMap E K (t j)) hq
    rw [eval_mul, eval_embForm_alt σ ht, eval_embForm_alt τ ht, eval_C, one_mul] at this
    exact this.symm
  rw [hr, C_1, mul_one] at hq
  refine AlgHom.ext_of_adjoin_eq_top hgen ?_
  rintro _ ⟨j, rfl⟩
  have := congrArg (eval (Pi.single j 1)) hq
  simpa [eval_embForm, Pi.single_apply] using this.symm
end GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
