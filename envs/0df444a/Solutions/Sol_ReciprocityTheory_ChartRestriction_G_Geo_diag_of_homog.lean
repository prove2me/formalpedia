-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.diag_of_homog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:12:27.866809+00:00
-- url     : https://prove2.me/submissions/d4d08ea2-1210-40dc-a495-670a4502a0e7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFibB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_weight_blkW
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_diag_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (d : ℕ) {f : MvPolynomial (Σ k, ι k) ℂ}
    (hf : IsWeightedHomogeneous (blkW ι) f (fun _ => d)) :
    ∃ G : MvPolynomial ((k : K) → ι k) ℂ, G.totalDegree ≤ d ∧
      ∀ z : (Σ k, ι k) → ℂ, eval z f = eval (segre z) G := by
  classical
  have hG : ∀ m : (Σ k, ι k) →₀ ℕ, ∃ G : MvPolynomial ((k : K) → ι k) ℂ,
      m ∈ f.support → G.totalDegree ≤ d ∧ ∀ z : (Σ k, ι k) → ℂ, ∏ p, z p ^ m p = eval (segre z) G := by
    intro m
    by_cases hm : m ∈ f.support
    · have hw := hf (mem_support_iff.1 hm)
      obtain ⟨G, h1, h2⟩ := diag_prod d (fun p => m p) (fun k => by
        have := congrFun hw k
        rwa [weight_blkW] at this)
      exact ⟨G, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hm⟩
  choose Gf hGf using hG
  refine ⟨∑ m ∈ f.support, C (coeff m f) * Gf m, ?_, fun z => ?_⟩
  · refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun m hm => ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact (hGf m hm).1
  · rw [eval_eq', map_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [eval_mul, eval_C, (hGf m hm).2 z]
end ReciprocityTheory.ChartRestriction.G.Geo
