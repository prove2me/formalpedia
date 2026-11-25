-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxB_gram_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:08:44.551143+00:00
-- url     : https://prove2.me/submissions/a1137cdf-517c-4cab-b86d-c23ad33c1d71

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_jForm_smul_right
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_jForm_sum_right
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_jForm_smul_left
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_jForm_sum_left
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_jForm_conj
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_jForm_self
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_jForm_self_re
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_graph_pos

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
      (w ≠ 0 → 0 < posSq p (∑ j, w j • X j))) :
    (Matrix.of fun k j : ApproxPosIdx r p => jForm p (X k.1) (X j.1)).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext k j
    simp [Matrix.conjTranspose_apply, approxB_jForm_conj]
  · have e : star x ⬝ᵥ ((Matrix.of fun k j : ApproxPosIdx r p => jForm p (X k.1) (X j.1)) *ᵥ x) =
        jForm p (∑ k, x k • X k.1) (∑ k, x k • X k.1) := by
      rw [approxB_jForm_sum_left]
      simp only [approxB_jForm_smul_left, approxB_jForm_sum_right, approxB_jForm_smul_right]
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum,
        Complex.star_def]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e, approxB_jForm_self]
    have h := (approxB_graph_pos hρ1 hρ X hg x).1
    rw [approxB_jForm_self_re] at h
    exact Complex.zero_le_real.mpr (by linarith)
end ReciprocityTheory.MultiplicativeHeights
