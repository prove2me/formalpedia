-- Prove2me | solution 1 for P2M_Formalism_GM_FrozenVariableComponents_coeff__shift_zero_bf4af767eaba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:29:35.358527+00:00
-- url     : https://prove2.me/submissions/02e65d1a-2563-4cc1-a3cb-4dbec775eebe

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
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
theorem _root_.solution (b : Fin r →₀ ℕ) (ρ : Fin r) (k : ℕ) (hb : ¬ Finsupp.single ρ k ≤ b)
    (G : MvPolynomial (Fin (N + 1) × Fin r) K) :
    coeffη b (X (Fin.last N, ρ) ^ k * G) = 0 := by
  refine MvPolynomial.induction_on' G (fun n a => ?_) (fun p q hp hq => ?_)
  · rw [coeffη_Xlast_pow_mul_monomial, if_neg]
    intro h
    exact hb (by rw [← h]; exact le_add_self)
  · simp only [mul_add, map_add, hp, hq, add_zero]
end Formalism.GM.FrozenVariableComponents
