-- Prove2me | solution 1 for PI.SqfRootsInj.W.orderOf_dvd_pow_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:32.436183+00:00
-- url     : https://prove2.me/submissions/20c86bd1-fe96-4388-89a4-2ca1a101304a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_WitBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_WitMain
import Theorems.Thm_P2M_PI_SqfRootsInj_W_pow_pred_eq_one__d29b6a46da77
import Theorems.Thm_PI_SqfRootsInj_W_pow_card_minpoly


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfRootsInj PI.SqfRootsInj.W
open PI.SqfLab
variable {g : ℕ} [Fact g.Prime]
namespace PI.SqfRootsInj.W
theorem _root_.solution {x : Fbar g} (hx0 : x ≠ 0) {e : ℕ}
    (he : (minpoly (ZMod g) x).natDegree = e) (he1 : 1 ≤ e) :
    g ^ e - 1 ≠ 0 ∧ orderOf x ∣ g ^ e - 1 := by
  have hg : 1 < g := (Fact.out : g.Prime).one_lt
  have hxe : x ^ (g ^ e) = x := he ▸ pow_card_minpoly x
  refine ⟨Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by omega) hg), ?_⟩
  exact orderOf_dvd_of_pow_eq_one (pow_pred_eq_one' hx0 (Nat.one_le_pow _ _ (by omega)) hxe)
end PI.SqfRootsInj.W
