-- Prove2me | solution 1 for SingularCardinals.sch_of_sch2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:25:36.083978+00:00
-- url     : https://prove2.me/submissions/a2cb1459-5139-4786-9f68-c92e6e5fb625

import Mathlib
import Definitions.Def_JechStationary
import Definitions.Def_SingularCardinals_basic

universe u

open Cardinal

set_option linter.deprecated false in
theorem S215SC_pow_cof (κ : Cardinal.{u})
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

theorem solution (h : SingularCardinals.SCH₂.{u}) : SingularCardinals.SCH.{u} := by
  intro κ hsing hlim
  have hcof : κ.ord.cof < κ := hsing.cof_ord_lt
  have h2 : 2 ^ κ.ord.cof < κ := hlim.two_power_lt hcof
  rw [← S215SC_pow_cof κ hsing hlim]
  exact h κ hsing h2
