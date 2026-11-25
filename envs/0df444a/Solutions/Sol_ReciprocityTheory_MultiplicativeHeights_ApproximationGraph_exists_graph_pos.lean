-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.exists_graph_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:17:32.102648+00:00
-- url     : https://prove2.me/submissions/00410e86-8fe6-4dea-ab40-8ce5d778d8bb

import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxGraphA
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxGraphB
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_posPart_posPart
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_posPart_negPart
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_negPart_posPart
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_negPart_negPart
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_posPart_zero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_negPart_zero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_posPart_supp
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_graph_bound
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_graphMap_apply
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_euc_eq_zero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_euc_zero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_negPart_add
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_posPart_add
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_posPart_add_negPart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
open ComplexConjugate
namespace ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
theorem _root_.solution {r p : ℕ} {μ ρ : ℝ} (X : Fin r → Fin r → ℂ) (hμ : 0 < μ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1)
    (hX : ∀ j : Fin r, (j : ℕ) < p →
      normSq (X j - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2)
    (b : Fin r → ℂ) : ∃ w : Fin r → ℂ, (∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) ∧
      posPart p (∑ j, w j • X j) = posPart p b := by

  have hinj : Function.Injective (graphMap p X) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    rw [graphMap_apply] at hu
    have hn : negPart p u = 0 := by
      have := congrArg (negPart p) hu
      rwa [negPart_add, negPart_posPart, zero_add, negPart_negPart, negPart_zero] at this
    have hp : posPart p (∑ j, posPart p u j • X j) = 0 := by
      have := congrArg (posPart p) hu
      rwa [posPart_add, posPart_posPart, posPart_negPart, add_zero, posPart_zero] at this
    have h2 := (graph_bound X hμ hρ hρ1 hX (posPart p u) (posPart_supp p u)).2
    rw [hp, euc_zero, norm_zero] at h2
    have hu0 : posPart p u = 0 := by
      rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr; exact Subsingleton.elim _ _
      · have hsq : 0 < √(r : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hr)
        have hle : ‖euc (posPart p u)‖ ≤ 0 := by
          by_contra hc
          push_neg at hc
          have := mul_pos (by norm_num : (0 : ℝ) < 3) (mul_pos (mul_pos hsq hμ) hc)
          linarith
        exact euc_eq_zero (norm_le_zero_iff.mp hle)
    rw [← posPart_add_negPart p u, hu0, hn, add_zero]
  obtain ⟨u, hu⟩ := (LinearMap.injective_iff_surjective.mp hinj) (posPart p b)
  refine ⟨posPart p u, posPart_supp p u, ?_⟩
  have := congrArg (posPart p) hu
  rwa [graphMap_apply, posPart_add, posPart_posPart, posPart_negPart, add_zero,
    posPart_posPart] at this
end ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
