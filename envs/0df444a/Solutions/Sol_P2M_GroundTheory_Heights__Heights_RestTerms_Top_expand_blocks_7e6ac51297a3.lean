-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_expand_blocks_7e6ac51297a3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:28:29.802123+00:00
-- url     : https://prove2.me/submissions/6918cdf8-0faf-434b-8a76-f4ffe5e8ba27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_fibreClass_eq_prod_76f68d661d7a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_smallBlockMu_eq_sum_6993d3b7b10d

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
theorem _root_.solution (f r a : ℕ) (c : SmallBlock) (g : Fin f → MvPolynomial (Fin r) ℚ) (e : ℕ) :
    (∏ σ, blockEmb f (r + a) σ (yEval r a c (g σ))) * smallBlockMu f r a c ^ e *
        fibreClass f r a c =
      ∑ m ∈ Finset.piAntidiag (Finset.univ : Finset (Fin f)) e,
        (Nat.multinomial Finset.univ m : ℚ) •
          ∏ σ, blockEmb f (r + a) σ
            (yEval r a c (g σ * psum (Fin r) ℚ 1 ^ m σ) * fib1 r a c) := by
  rw [smallBlockMu_eq_sum, Finset.sum_pow_eq_sum_piAntidiag, fibreClass_eq_prod, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  simp only [map_mul, map_pow, Finset.prod_mul_distrib]
  ring
end GroundTheory.Heights₂.Heights.RestTerms.Top
