-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_schur_1cba2d0c1248
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:39:31.326748+00:00
-- url     : https://prove2.me/submissions/e0df2b58-25b6-4f52-8a45-c463531410a1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_of_dividedDifference_eq_219f21cc1918

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
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Top
theorem _root_.solution (hB : LemmaB.Statement) (r a : ℕ) (c : SmallBlock) :
    ∃ κ : ℚ, (κ = (r.factorial : ℚ) * a.factorial ∨ κ = -((r.factorial : ℚ) * a.factorial)) ∧
      ∀ lam : Fin r → ℕ, Antitone lam →
        HasDD 1 (r + a) (yEval r a c (schur (Fin r) lam) * fib1 r a c) (pushOut r a c κ lam) := by
  obtain ⟨κ, hκ, h⟩ := hB r a c
  refine ⟨κ, hκ, fun lam hl => hasDD_of_dividedDifference_eq ?_⟩
  have := h lam hl
  rw [yEval, fib1, ← mul_assoc, this, pushOut, xSign]
  split_ifs <;> simp
end GroundTheory.Heights₂.Heights.RestTerms.Top
