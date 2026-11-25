-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_isSmallH_monomial_8a2ada881a14
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:27:31.846409+00:00
-- url     : https://prove2.me/submissions/7ee74fe3-0174-4ce1-bec4-c764c0e6629b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_MonomialValuesOneBlock
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_aeval_monomial_one_537b40e9e860
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_isMultiHomog_monomial_5f3d43776f81
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_monomial_bound_07979692c060
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_add_95ee52bfb1b9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_mul_0d39b8f19b1f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_mem_mCoordIdeal_of_aeval_eq_zero_09693c41a4b2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.SpanningAtDominantWeight
variable {ι : Type} [Fintype ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.SpanningAtDominantWeight
theorem _root_.solution {Ω : Type} [Field Ω] (y : Coord n → Ω) (A : Geo.HermLine (blockIdx n)) (b : ι → ℕ)
    (hAa : ∀ k, A.a k = b k)
    (hA : Geo.MonomialsBounded (ι := blockIdx n) (Geo.mCoordIdeal (ι := blockIdx n) y) A b) (τ : ℕ)
    (μ : Coord n →₀ ℕ) (hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = (τ • b) k) :
    Geo.IsSmallH (ι := blockIdx n) (Geo.mCoordIdeal (ι := blockIdx n) y) y A τ (∏ p, y p ^ μ p) := by
  intro dg dh g h z hg hh hd hgh hz
  have hdeg : dg = τ • b + dh := by
    funext k
    have := hd k
    rw [hAa k] at this
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact_mod_cast (by linarith : (dg k : ℤ) = τ * b k + dh k)
  have hmh := LowerBoundFree.isMultiHomog_mul (isMultiHomog_monomial μ (τ • b) hμ) hh
  rw [← hdeg] at hmh
  have hneg : Geo.IsMultiHomog (ι := blockIdx n) (-(monomial μ (1 : ℤ) * h)) dg :=
    fun m hm ↦ hmh m (by simpa using hm)
  have hF := LowerBoundFree.isMultiHomog_add hg hneg
  have hF0 : aeval y (g + -(monomial μ (1 : ℤ) * h)) = 0 := by
    rw [map_add, map_neg, map_mul, aeval_monomial_one, hgh]
    ring
  have hz0 := hz.2 _ (LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero y hF hF0)
  have hmz : eval z (map (Int.castRingHom ℂ) (monomial μ (1 : ℤ))) = ∏ p, z p ^ μ p := by
    rw [map_monomial, eval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), map_one, one_mul]
  rw [map_add, map_neg, map_mul, eval_add, eval_neg, eval_mul, hmz, add_neg_eq_zero] at hz0
  rw [hz0, norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (monomial_bound hA hz τ μ hμ) (norm_nonneg _)
end GroundTheory.Heights₂.Heights.SpanningAtDominantWeight
