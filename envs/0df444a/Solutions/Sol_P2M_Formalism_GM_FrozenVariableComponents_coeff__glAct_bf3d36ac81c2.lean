-- Prove2me | solution 1 for P2M_Formalism_GM_FrozenVariableComponents_coeff__glAct_bf3d36ac81c2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:47:59.985036+00:00
-- url     : https://prove2.me/submissions/09d9fc13-ab88-47b1-a120-1c86ad958535

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_coeff__X_castSucc_mul_a41a5a9118e3
import Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_coeff__pderiv_castSucc_bf4fdb97c4a1
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_glAct_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_snoc_vec_castSucc
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
open MvPolynomial Finset Formalism.GM.M
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.FrozenVariableComponents
theorem _root_.solution (LL : Letters N) (n j : ℕ) (hj : j ≤ N) (c d : Fin r) (b : Fin r →₀ ℕ)
    (F : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) :
    coeffη b (glAct p (LL.snoc n) j c d F) = glAct p LL j c d (coeffη b F) := by
  rw [glAct_apply, glAct_apply, Fin.sum_univ_castSucc, map_add, map_sum,
    if_neg (show ¬ ((Fin.last N : ℕ) < j) by rw [Fin.val_last]; omega), map_zero, add_zero]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Fin.coe_castSucc, snoc_vec_castSucc]
  split_ifs <;> simp [coeffη_X_castSucc_mul, coeffη_pderiv_castSucc]
end Formalism.GM.FrozenVariableComponents
