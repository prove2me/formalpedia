-- Prove2me | solution 1 for SoficGroups.KunPositiveWordMidrankEnergy.squaredPermutationEnergy_mul_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/e05dda3c-b77a-41bc-badc-473b974b06d4

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunPositiveWordMidrankEnergy_squaredPermutationEnergy_nonneg
import Theorems.Thm_SoficGroups_KunPositiveWordMidrankEnergy_squaredPermutationEnergy_mul_le

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunPositiveWordMidrankEnergy
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunPositiveWordMidrankEnergy
theorem _root_.solution
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    (f : (n : ℕ) → V n → ℝ)
    (p q : (n : ℕ) → Equiv.Perm (V n))
    (hp : Tendsto
      (fun n => squaredPermutationEnergy (f n) (p n) /
        Fintype.card (V n)) atTop (𝓝 0))
    (hq : Tendsto
      (fun n => squaredPermutationEnergy (f n) (q n) /
        Fintype.card (V n)) atTop (𝓝 0)) :
    Tendsto
      (fun n => squaredPermutationEnergy (f n) (p n * q n) /
        Fintype.card (V n)) atTop (𝓝 0) := by
  have hupper : Tendsto
      (fun n =>
        2 * (squaredPermutationEnergy (f n) (p n) /
          Fintype.card (V n)) +
        2 * (squaredPermutationEnergy (f n) (q n) /
          Fintype.card (V n))) atTop (𝓝 0) := by
    simpa using
      (Filter.Tendsto.const_mul (2 : ℝ) hp).add
        (Filter.Tendsto.const_mul (2 : ℝ) hq)
  refine squeeze_zero (fun n =>
    div_nonneg (squaredPermutationEnergy_nonneg (f n) (p n * q n))
      (Nat.cast_nonneg _)) ?_ hupper
  intro n
  calc
    squaredPermutationEnergy (f n) (p n * q n) /
        Fintype.card (V n) ≤
      (2 * squaredPermutationEnergy (f n) (p n) +
        2 * squaredPermutationEnergy (f n) (q n)) /
          Fintype.card (V n) :=
      div_le_div_of_nonneg_right
        (squaredPermutationEnergy_mul_le (f n) (p n) (q n))
        (Nat.cast_nonneg _)
    _ = 2 * (squaredPermutationEnergy (f n) (p n) /
          Fintype.card (V n)) +
        2 * (squaredPermutationEnergy (f n) (q n) /
          Fintype.card (V n)) := by ring
end SoficGroups.KunPositiveWordMidrankEnergy
