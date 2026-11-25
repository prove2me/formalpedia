-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.TorusLexOrder.integrable_torus_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:24:03.935873+00:00
-- url     : https://prove2.me/submissions/08cd67af-d3cd-49f7-b40b-3564f86b11be

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusLexB
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusLexC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_TorusLexOrder_continuous_eval_torus
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_TorusLexOrder_continuous_torusPoint
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_TorusLexOrder_integrable_of_bdd
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_TorusLexOrder_norm_eval_torus_le
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_TorusLexOrder_norm_torusPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
open MeasureTheory ComplexConjugate
private theorem norm_torusMono_eq_one {ι : Type} [Fintype ι] (θ : ι → ℝ) (s : ι →₀ ℕ) :
    ‖torusMono θ s‖ = 1 := by
  unfold torusMono
  rw [norm_prod]
  simp [norm_pow, norm_torusPoint]
private theorem continuous_torusMono' {ι : Type} [Fintype ι] (s : ι →₀ ℕ) :
    Continuous (fun θ : ι → ℝ => torusMono θ s) := by
  have h : ∀ i, Continuous fun θ : ι → ℝ => torusPoint θ i :=
    fun i => (continuous_apply i).comp continuous_torusPoint
  unfold torusMono
  exact continuous_finset_prod _ (fun i _ => (h i).pow _)
end ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
open MeasureTheory ComplexConjugate
namespace ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
theorem _root_.solution {ι : Type} [Fintype ι] (f : MvPolynomial ι ℂ) (s : ι →₀ ℕ) :
    Integrable (fun θ => MvPolynomial.eval (torusPoint θ) f * conj (torusMono θ s))
      (torusProb ι) := by
  refine integrable_of_bdd ((continuous_eval_torus f).mul
    (Complex.continuous_conj.comp (continuous_torusMono' s))) (∑ t ∈ f.support, ‖f.coeff t‖)
    (fun θ => ?_)
  have h := norm_eval_torus_le f θ
  simpa [norm_torusMono_eq_one] using h
end ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
