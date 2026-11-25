-- Prove2me | solution 1 for ReciprocityTheory.Cheb.rsgn_mul_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:10:06.947147+00:00
-- url     : https://prove2.me/submissions/0c7e4741-f378-4cde-8f00-ee5de8272046

import Definitions.Def_ReciprocityTheory_Chebotarev_Ucoord
import Definitions.Def_ReciprocityTheory_Chebotarev_DiscreteTopologyLatOf
import Theorems.Thm_ReciprocityTheory_Cheb_embZ_apply
import Theorems.Thm_ReciprocityTheory_Cheb_latOf_sign_prod
import Theorems.Thm_ReciprocityTheory_Cheb_normQ_eq_prod_places

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
open NumberField.InfinitePlace
namespace ReciprocityTheory.Cheb
theorem _root_.solution (α : 𝓞 E) : rsgn (embZ α) * Algebra.norm ℤ α = |Algebra.norm ℤ α| := by
  by_cases hα : α = 0
  · simp [hα]
  have hx : (α : E) ≠ 0 := by exact_mod_cast hα
  have hN : ((Algebra.norm ℤ α : ℤ) : ℝ) = (∏ w : {w : InfinitePlace E // w.IsReal}, embedding_of_isReal w.2 (α : E)) *
      ∏ w : {w : InfinitePlace E // w.IsComplex}, (w.1 (α : E)) ^ 2 := by
    rw [← normQ_eq_prod_places, ← Algebra.coe_norm_int]
    push_cast
    rfl
  have hsg : ((rsgn (embZ α) : ℤ) : ℝ) = ((SignType.sign ((Algebra.norm ℤ α : ℤ) : ℝ) : SignType) : ℝ) := by
    rw [hN, sign_mul, latOf_sign_prod, latOf_sign_prod]
    have hc : ∀ w : {w : InfinitePlace E // w.IsComplex}, SignType.sign ((w.1 (α : E)) ^ 2) = 1 := by
      intro w
      exact sign_pos (pow_pos (pos_iff.mpr hx) 2)
    simp only [hc, Finset.prod_const_one, mul_one]
    simp only [rsgn, embZ_apply, mixedEmbedding_apply_isReal, Int.cast_prod]
    simp only [SignType.intCast_cast]
    exact (map_prod (SignType.castHom : SignType →*₀ ℝ) _ _).symm
  have key : ((rsgn (embZ α) * Algebra.norm ℤ α : ℤ) : ℝ) = ((|Algebra.norm ℤ α| : ℤ) : ℝ) := by
    push_cast
    rw [hsg, sign_mul_self]
  exact_mod_cast key
end ReciprocityTheory.Cheb
