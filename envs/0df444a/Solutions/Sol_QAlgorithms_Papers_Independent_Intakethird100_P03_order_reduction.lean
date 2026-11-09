-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P03.order_reduction
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T11:16:57.855093+00:00
-- url     : https://prove2.me/submissions/c949a006-4b67-4bf8-9388-07616a1e1a4f

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P03

noncomputable section

open scoped Matrix ComplexConjugate Kronecker

open QAlgorithms.Papers.Independent.Renew46.P01 (cleanVector)

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Intakethird100.P03 in
theorem solution (q : ℕ) (hq : 2 ≤ q) (g : (ZMod q)ˣ) :
    0 < orderOf g ∧
    (∀ m : ℤ, orderAction g m 1 = 1 ↔ ∃ t : ℤ, m = (orderOf g : ℤ) * t) ∧
    orderAction g (orderOf g : ℤ) 1 = 1 ∧
    ∀ r : ℕ, 0 < r → orderAction g (r : ℤ) 1 = 1 → orderOf g ≤ r := by
  haveI : NeZero q := ⟨by omega⟩
  have key : ∀ m : ℤ, orderAction g m 1 = 1 ↔ (orderOf g : ℤ) ∣ m := by
    intro m
    unfold orderAction
    rw [mul_one, Units.val_eq_one, orderOf_dvd_iff_zpow_eq_one]
  refine ⟨orderOf_pos g, fun m => (key m).trans ⟨fun ⟨t, ht⟩ => ⟨t, ht⟩, fun ⟨t, ht⟩ => ⟨t, ht⟩⟩,
    (key _).mpr dvd_rfl, fun r hr h => ?_⟩
  have := (key r).mp h
  exact Nat.le_of_dvd hr (Int.natCast_dvd_natCast.mp this)

end
