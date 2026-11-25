-- Prove2me | solution 1 for PI.Dv.GLP.char_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:56:07.087733+00:00
-- url     : https://prove2.me/submissions/fbb8a0fb-757e-40fb-bab3-ed6090d04549

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_FinrankIntertw
import Theorems.Thm_PI_Dv_GLP_finrank_intertw
import Theorems.Thm_PI_Dv_GLP_card_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLP
open Representation
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.GLP
theorem _root_.solution [CharZero K] (T : GoodSet K G) (s t : T.S) :
    ∑ g : G, LinearMap.trace K _ (T.tau t g) * LinearMap.trace K _ (T.tau s g⁻¹) =
      if s = t then ((Fintype.card G : ℕ) : K) else 0 := by
  have hG : ((Nat.card G : ℕ) : K) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]; exact card_ne_zero
  haveI : Invertible ((Nat.card G : ℕ) : K) := invertibleOfNonzero hG
  have h := Representation.card_inv_mul_sum_char_mul_char_eq_finrank (T.tau s) (T.tau t)
  rw [finrank_intertw] at h
  simp only [Representation.character] at h
  rw [inv_mul_eq_iff_eq_mul₀ hG] at h
  rw [h, Nat.card_eq_fintype_card]
  split_ifs <;> simp
end PI.Dv.GLP
