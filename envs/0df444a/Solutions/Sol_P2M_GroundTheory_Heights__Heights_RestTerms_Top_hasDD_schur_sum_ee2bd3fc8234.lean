-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_schur_sum_ee2bd3fc8234
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:29:10.905207+00:00
-- url     : https://prove2.me/submissions/b87c84f6-6c3d-4b04-ad14-96573d8d86e0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_smul_1cdeb56450cd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_sum_332cef462e63

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
theorem _root_.solution (r a : ℕ) (c : SmallBlock) (κ : ℚ)
    (hκ : ∀ lam : Fin r → ℕ, Antitone lam →
        HasDD 1 (r + a) (yEval r a c (schur (Fin r) lam) * fib1 r a c) (pushOut r a c κ lam))
    (s : Finset (Fin r → ℕ)) (hs : ∀ lam ∈ s, Antitone lam) (b : (Fin r → ℕ) → ℚ) :
    HasDD 1 (r + a) (yEval r a c (∑ lam ∈ s, C (b lam) * schur (Fin r) lam) * fib1 r a c)
      (∑ lam ∈ s, b lam • pushOut r a c κ lam) := by
  rw [map_sum, Finset.sum_mul]
  refine hasDD_sum s fun lam hlam => ?_
  have := hasDD_smul (b lam) (hκ lam (hs lam hlam))
  convert this using 1
  rw [map_mul, yEval, aeval_C, Algebra.smul_def, mul_assoc]
end GroundTheory.Heights₂.Heights.RestTerms.Top
