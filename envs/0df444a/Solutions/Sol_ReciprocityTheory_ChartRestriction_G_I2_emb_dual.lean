-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.emb_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:28:47.7847+00:00
-- url     : https://prove2.me/submissions/e4978893-d416-4391-bc29-4a19a6c0aa62

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitVM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitVA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitVB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_trace_sum_emb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_im_Hf_act
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_emb_indep


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex Module
noncomputable section
variable {E : Type} [Field E] [NumberField E]
variable {dim : (E →+* ℂ) → ℕ}
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (x ξ : Vsp dim) (y : E)
    (hy : ∀ β : 𝓞 E, ((Algebra.trace ℚ E ((β : E) * y) : ℚ) : ℝ) = (Hf x (act β ξ)).im) (σ : E →+* ℂ) :
    σ y = (hA x ξ (ComplexEmbedding.conjugate σ) - (starRingEnd ℂ) (hA x ξ σ)) / (2 * I) := by
  have h := emb_indep (fun σ => σ y -
      (hA x ξ (ComplexEmbedding.conjugate σ) - (starRingEnd ℂ) (hA x ξ σ)) / (2 * I)) (fun β => by
    have h1 := congrArg (fun r : ℝ => (r : ℂ)) (hy β)
    simp only [Complex.ofReal_ratCast] at h1
    rw [trace_sum_emb, im_Hf_act] at h1
    simp only [map_mul] at h1
    simp only [mul_sub, Finset.sum_sub_distrib, h1, sub_self])
  have := congrFun h σ
  simpa [sub_eq_zero] using this
end ReciprocityTheory.ChartRestriction.G.I2
