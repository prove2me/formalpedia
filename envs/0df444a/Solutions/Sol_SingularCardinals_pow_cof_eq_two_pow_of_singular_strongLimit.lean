-- Prove2me | solution 1 for SingularCardinals.pow_cof_eq_two_pow_of_singular_strongLimit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T12:36:23.499105+00:00
-- url     : https://prove2.me/submissions/6a173def-c76f-41b0-9b3f-47f3779dc372

import Mathlib
import Definitions.Def_JechStationary
import Definitions.Def_SingularCardinals_basic

universe u

open Cardinal

set_option linter.deprecated false in
theorem solution (κ : Cardinal.{u})
    (hsing : κ.IsSingular) (hlim : IsStrongLimit κ) :
    κ ^ κ.ord.cof = 2 ^ κ := by
  have hinf : ℵ₀ ≤ κ := hsing.aleph0_le
  have hκ0 : κ ≠ 0 := fun h => by
    rw [h] at hinf; exact absurd hinf (not_le.mpr aleph0_pos)
  apply le_antisymm
  · calc κ ^ κ.ord.cof ≤ κ ^ κ := power_le_power_left hκ0 (Ordinal.cof_ord_le κ)
      _ = 2 ^ κ := power_self_eq hinf
  · obtain ⟨ι, f, hf, hι⟩ := Ordinal.exists_lsub_cof κ.ord
    have hfi : ∀ i, Order.succ (f i) < κ.ord := fun i =>
      (Cardinal.isSuccLimit_ord hinf).succ_lt (hf ▸ Ordinal.lt_lsub f i)
    have hlt : ∀ i, (Order.succ (f i)).card < κ := fun i => Cardinal.lt_ord.mp (hfi i)
    have hsum : κ ≤ Cardinal.sum fun i => (Order.succ (f i)).card := by
      have h := Ordinal.card_iSup_le_sum_card.{u, u} (fun i => Order.succ (f i))
      have : (⨆ i, Order.succ (f i)) = κ.ord := hf
      rw [this, Cardinal.card_ord] at h
      exact h
    calc (2 : Cardinal.{u}) ^ κ ≤ 2 ^ (Cardinal.sum fun i => (Order.succ (f i)).card) :=
          power_le_power_left two_ne_zero hsum
      _ = Cardinal.prod fun i => (2 : Cardinal.{u}) ^ (Order.succ (f i)).card := power_sum _ _
      _ ≤ Cardinal.prod fun _ : ι => κ := prod_le_prod _ _ fun i => (hlim.two_power_lt (hlt i)).le
      _ = κ ^ #ι := prod_const' _ _
      _ = κ ^ κ.ord.cof := by rw [hι]
