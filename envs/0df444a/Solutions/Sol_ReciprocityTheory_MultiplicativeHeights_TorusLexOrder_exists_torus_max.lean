-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.TorusLexOrder.exists_torus_max
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:30:01.933159+00:00
-- url     : https://prove2.me/submissions/fb563ccd-fd0c-463a-ac5b-6af9e3b8af5f

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusLexB
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusLexC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_TorusLexOrder_torusPoint_fract
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_TorusLexOrder_continuous_eval_torus


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
theorem _root_.solution {ι : Type} [Fintype ι] (f : MvPolynomial ι ℂ) :
    ∃ θ₀ : ι → ℝ, ∀ θ, ‖MvPolynomial.eval (torusPoint θ) f‖ ≤
      ‖MvPolynomial.eval (torusPoint θ₀) f‖ := by
  obtain ⟨θ₀, -, hθ₀⟩ := (isCompact_univ_pi (fun _ : ι => isCompact_Icc (a := (0 : ℝ)) (b := 1))).exists_isMaxOn
    ⟨fun _ => 0, fun i _ => by simp⟩ (continuous_eval_torus f).norm.continuousOn
  refine ⟨θ₀, fun θ => ?_⟩
  have hmem : (fun i => Int.fract (θ i)) ∈ Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1) :=
    fun i _ => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have h := isMaxOn_iff.mp hθ₀ _ hmem
  simp only [torusPoint_fract] at h
  exact h
end ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
