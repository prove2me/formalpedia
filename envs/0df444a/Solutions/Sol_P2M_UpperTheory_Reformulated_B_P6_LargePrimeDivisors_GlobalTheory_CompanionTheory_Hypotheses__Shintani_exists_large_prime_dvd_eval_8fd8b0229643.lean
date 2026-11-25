-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_P6_LargePrimeDivisors_GlobalTheory_CompanionTheory_Hypotheses__Shintani_exists_large_prime_dvd_eval_8fd8b0229643
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:19:53.135827+00:00
-- url     : https://prove2.me/submissions/f5f87c38-6a37-4fc2-b67b-6d3be5f4aaaf

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_LargePrimeDivisors
import Theorems.Thm_UpperTheory_Reformulated_B_P6_LargePrimeDivisors_exists_prime_gt_dvd_eval_of_natDegree_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.P6 UpperTheory.Reformulated.B.P6.LargePrimeDivisors
open scoped Int LT OfNat Polynomial Dvd
namespace UpperTheory.Reformulated.B.P6.LargePrimeDivisors
namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
theorem _root_.solution :
    ∀ (f : Polynomial ℤ), OfNat.ofNat (nat_lit 0) < f.natDegree → ∀ (N : ℕ), ∃ (p : ℕ) (m : ℤ), Nat.Prime p ∧ N < p ∧ p.cast ∣ Polynomial.eval m f := by
  intro f hf N
  exact exists_prime_gt_dvd_eval_of_natDegree_pos f hf N
end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
end UpperTheory.Reformulated.B.P6.LargePrimeDivisors
