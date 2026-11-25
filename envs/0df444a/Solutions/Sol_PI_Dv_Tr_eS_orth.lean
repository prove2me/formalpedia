-- Prove2me | solution 1 for PI.Dv.Tr.eS_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:24:42.946374+00:00
-- url     : https://prove2.me/submissions/fe280689-d486-4648-aedf-2266191229db

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
import Theorems.Thm_PI_Dv_Tr_eS_comm
import Theorems.Thm_P2M_PI_Dv_Tr_finrank_pos__519d460918af
import Theorems.Thm_PI_Dv_Tr_eS_mul_eS_of_ne_zero
import Theorems.Thm_PI_Dv_Tr_eS_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open PI.Dv
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.Tr
theorem _root_.solution (T : GoodSet K G) (s t : T.S) (hst : s ≠ t) : eS T s * eS T t = 0 := by
  by_contra h
  have h1 := eS_mul_eS_of_ne_zero T s t h
  have h' : eS T t * eS T s ≠ 0 := by rw [← eS_comm]; exact h
  have h2 := eS_mul_eS_of_ne_zero T t s h'
  have heq : eS T s = eS T t := by rw [← h2, ← eS_comm, h1]
  apply hst
  apply T.inj
  have hG : ((Fintype.card G : ℕ) : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h1' := congrArg (fun f => MonoidAlgebra.coeff f 1) heq
  simp only [eS_apply, inv_one, map_one, LinearMap.trace_one, cf] at h1'
  have hd : Module.finrank K (T.W s) = Module.finrank K (T.W t) := by
    field_simp at h1'
    have : ((Module.finrank K (T.W s) : ℕ) : K) ^ 2 = ((Module.finrank K (T.W t) : ℕ) : K) ^ 2 := by
      linear_combination h1'
    have h2' : Module.finrank K (T.W s) ^ 2 = Module.finrank K (T.W t) ^ 2 := by exact_mod_cast this
    exact Nat.pow_left_injective (by norm_num) h2'
  change (fun g => LinearMap.trace K (T.W s) (T.tau s g)) = (fun g => LinearMap.trace K (T.W t) (T.tau t g))
  funext g
  have hx := congrArg (fun f => MonoidAlgebra.coeff f g⁻¹) heq
  simp only [eS_apply, inv_inv, cf, hd] at hx
  have hd0 : ((Module.finrank K (T.W t) : ℕ) : K) ≠ 0 := by exact_mod_cast (finrank_pos' T t).ne'
  have hne : ((Module.finrank K (T.W t) : ℕ) : K) / ((Fintype.card G : ℕ) : K) ≠ 0 := div_ne_zero hd0 hG
  exact mul_left_cancel₀ hne hx
end PI.Dv.Tr
