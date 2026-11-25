-- Prove2me | solution 1 for P2M_Formalism_GM_FrozenVariableComponents_coeff__shift_360bf627fe39
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:55:26.972267+00:00
-- url     : https://prove2.me/submissions/b03c30ce-e81b-49cb-b135-203a2d8ef9c3

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_coeff__monomial_8358895534d9
import Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_coeff__Xlast_pow_mul_monomial_6ca4897b8fd3
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb

set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset
variable {K : Type*} [CommRing K] {N r : ℕ}
namespace Formalism.GM.FrozenVariableComponents
theorem _root_.solution (b : Fin r →₀ ℕ) (ρ : Fin r) (k : ℕ) (G : MvPolynomial (Fin (N + 1) × Fin r) K) :
    coeffη (b + Finsupp.single ρ k) (X (Fin.last N, ρ) ^ k * G) = coeffη b G := by
  refine MvPolynomial.induction_on' G (fun n a => ?_) (fun p q hp hq => ?_)
  · rw [coeffη_Xlast_pow_mul_monomial, coeffη_monomial]
    simp only [add_left_inj]
  · simp only [mul_add, map_add, hp, hq]
end Formalism.GM.FrozenVariableComponents
