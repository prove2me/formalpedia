-- Prove2me | solution 1 for P2M_GlobalTheory_T_coeff_aeval_one_add_X_pow_sub_one_ne_zero__677c239f9cf3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:32:35.642808+00:00
-- url     : https://prove2.me/submissions/b0cb3ea7-2d30-4890-ade0-6cba3af3e2a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CoeffAevalOneAddXPowSubOneNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CoeffAevalOneAddXPowSubOneNeZeroStatement
import Theorems.Thm_GlobalTheory_coeff_aeval_one_add_X_pow_sub_one_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k σ : Type) [Field k] [Fintype σ] (l M : ℕ) [Fact l.Prime] [CharP k l] (D u : MvPolynomial σ k) (n e : σ → ℕ), u.coeff 0 ≠ 0 → D - u * ∏ q, MvPolynomial.X q ^ n q ∈ Ideal.span (Set.range fun q : σ => (MvPolynomial.X q : MvPolynomial σ k) ^ (l ^ M)) → ∑ q, n q * l ^ e q < l ^ M → (MvPolynomial.aeval (fun q => (1 + Polynomial.X : Polynomial k) ^ (l ^ e q) - 1) D).coeff (∑ q, n q * l ^ e q) ≠ 0 := by
  first | exact @GlobalTheory.coeff_aeval_one_add_X_pow_sub_one_ne_zero | exact GlobalTheory.coeff_aeval_one_add_X_pow_sub_one_ne_zero | (intros; apply GlobalTheory.coeff_aeval_one_add_X_pow_sub_one_ne_zero <;> assumption)
end _root_.GlobalTheory.T
