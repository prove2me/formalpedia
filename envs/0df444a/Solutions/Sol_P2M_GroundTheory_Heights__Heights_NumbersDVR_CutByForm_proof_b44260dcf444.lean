-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_CutByForm_proof_b44260dcf444
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:06:17.367017+00:00
-- url     : https://prove2.me/submissions/d28f6352-6231-483d-b3cf-222764d7f54a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PCutByForm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_sup_span_of_form_8aa08999bb53
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_withBot_lt_of_add_one_lt_6fdcb3f5460f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_idealCycle_4d914ac33675


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace CutByForm
theorem _root_.solution (h1 : IntNumAssoc.Statement.{u}) (h2 : HilbFnCut.Statement.{u})
    (h3 : MixedDiffLinear.Statement) : CutByForm.Statement.{u} := by
  intro F _ K _ _ ι _ n G hGp hG hdim s c hs hsG bs
  have : G.IsPrime := hGp
  set J : Ideal (MRing ι F) := G ⊔ Ideal.span {s} with hJdef
  set c' : K → ℤ := fun k => (c k : ℤ) with hc'

  have hnzd : ∀ y, s * y ∈ G → y ∈ G := fun y hy => (hGp.mem_or_mem hy).resolve_left hsG
  have hH : hilbFn J = diffStep c' (hilbFn G) := by
    funext m
    exact h2 F K ι G s c hG hs hnzd m

  have hnum : intNum F G (Matrix.vecCons c' bs) = intNum F J bs := by
    obtain ⟨-, -, -, h4, h5⟩ := h3 K n bs (hilbFn G) (hilbFn G) 0 0 c'
    unfold intNum
    rw [h5, ← h4, hH]

  have hJ : IsMultiHomogIdeal J := isMultiHomogIdeal_sup_span_of_form hG hs

  have hle : G ≤ J := le_sup_left
  have hr : Ideal.Quotient.mk G s ∈ nonZeroDivisors (MRing ι F ⧸ G) :=
    mem_nonZeroDivisors_of_ne_zero fun h => hsG (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hsucc : ringKrullDim (MRing ι F ⧸ J) + 1 ≤ ringKrullDim (MRing ι F ⧸ G) :=
    ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hle)
      (Ideal.Quotient.factor_surjective hle) hr (by
        rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_sup_right (Ideal.subset_span rfl))
  have hdimJ : ringKrullDim (MRing ι F ⧸ J) <
      ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    apply withBot_lt_of_add_one_lt
    have he : n + 1 + Fintype.card K + 1 = n + 2 + Fintype.card K := by omega
    rw [he]
    exact lt_of_le_of_lt hsucc hdim

  rw [hnum, h1 F K ι n J hJ hdimJ bs, divCycle_eq_idealCycle]
end CutByForm
end GroundTheory.Heights₂.Heights.NumbersDVR
