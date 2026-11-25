-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.TorusLexOrder.torus_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:46:27.710549+00:00
-- url     : https://prove2.me/submissions/9582e4ad-96ca-4200-9148-3f00db698755

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusLexB
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_TorusLexOrder_torus_one_dim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
open MeasureTheory ComplexConjugate
namespace ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
theorem _root_.solution {ι : Type} [Fintype ι] (s t : ι →₀ ℕ) :
    ∫ θ, torusMono θ t * conj (torusMono θ s) ∂(torusProb ι) = if t = s then 1 else 0 := by
  classical
  have h : ∀ θ : ι → ℝ, torusMono θ t * conj (torusMono θ s) =
      ∏ i, torusFactor (t i) (s i) (θ i) := by
    intro θ
    simp only [torusMono, torusFactor, torusPoint, map_prod, map_pow, ← Finset.prod_mul_distrib]
  simp_rw [h]
  rw [torusProb, integral_fintype_prod_eq_prod (f := fun i x => torusFactor (t i) (s i) x)]
  simp_rw [torus_one_dim]
  split_ifs with hts
  · subst hts; simp
  · have : ∃ i, t i ≠ s i := by
      by_contra hc; push_neg at hc; exact hts (Finsupp.ext hc)
    obtain ⟨i, hi⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
end ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
