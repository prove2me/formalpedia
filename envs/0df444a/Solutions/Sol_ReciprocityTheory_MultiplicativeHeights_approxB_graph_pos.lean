-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxB_graph_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:55:08.465843+00:00
-- url     : https://prove2.me/submissions/96a40875-8cb7-49e6-ba61-a454bb8bdb9f

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_posSq_nonneg
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_jForm_self_re
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_pad_sum
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_pad_ne
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_pad_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {r p : ℕ} {ρ : ℝ} (hρ1 : ρ ≤ 1) (hρ : 0 < ρ) (X : Fin r → Fin r → ℂ)
    (hg : ∀ w : Fin r → ℂ, (∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) →
      negSq p (∑ j, w j • X j) ≤ (ρ / 3) ^ 2 * posSq p (∑ j, w j • X j) ∧
      (w ≠ 0 → 0 < posSq p (∑ j, w j • X j)))
    (x : ApproxPosIdx r p → ℂ) :
    0 ≤ (jForm p (∑ k, x k • X k.1) (∑ k, x k • X k.1)).re ∧
    (x ≠ 0 → 0 < (jForm p (∑ k, x k • X k.1) (∑ k, x k • X k.1)).re) := by
  obtain ⟨h1, h2⟩ := hg (approxPadPos x) (fun j hj => approxB_pad_zero x j hj)
  rw [approxB_pad_sum] at h1 h2
  rw [approxB_jForm_self_re]
  have hρ' : (ρ / 3) ^ 2 ≤ 1 / 9 := by
    have h3 : ρ / 3 ≤ 1 / 3 := by linarith
    have h4 : 0 ≤ ρ / 3 := by linarith
    nlinarith
  have hp0 := approxB_posSq_nonneg p (∑ k, x k • X k.1)
  refine ⟨by nlinarith, fun hx => ?_⟩
  have h5 := h2 (approxB_pad_ne x hx)
  nlinarith
end ReciprocityTheory.MultiplicativeHeights
