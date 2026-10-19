-- Prove2me | solution 1 for SoficGroups.KunPositiveWordMidrankEnergy.squaredPermutationEnergy_tendsto_of_normalizedHamming
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/e5d0e4d6-0776-4132-938b-d7201352ae6d

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunPositiveWordMidrankEnergy_squaredPermutationEnergy_nonneg
import Theorems.Thm_SoficGroups_KunPositiveWordMidrankEnergy_squaredPermutationEnergy_le_add_hammingDist

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunPositiveWordMidrankEnergy
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunPositiveWordMidrankEnergy
theorem _root_.solution
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (f : (n : ℕ) → V n → ℝ)
    (hf0 : ∀ n x, 0 ≤ f n x)
    (hf1 : ∀ n x, f n x ≤ 1)
    (p q : (n : ℕ) → Equiv.Perm (V n))
    (hq : Tendsto
      (fun n => squaredPermutationEnergy (f n) (q n) /
        Fintype.card (V n)) atTop (𝓝 0))
    (hd : Tendsto
      (fun n => SoficGroups.normalizedHamming (p n) (q n))
      atTop (𝓝 0)) :
    Tendsto
      (fun n => squaredPermutationEnergy (f n) (p n) /
        Fintype.card (V n)) atTop (𝓝 0) := by
  have hupper : Tendsto
      (fun n => squaredPermutationEnergy (f n) (q n) /
        Fintype.card (V n) +
          SoficGroups.normalizedHamming (p n) (q n))
      atTop (𝓝 0) := by
    simpa only [add_zero] using hq.add hd
  refine squeeze_zero (fun n =>
    div_nonneg (squaredPermutationEnergy_nonneg (f n) (p n))
      (Nat.cast_nonneg _)) ?_ hupper
  intro n
  have he := squaredPermutationEnergy_le_add_hammingDist
    (f n) (hf0 n) (hf1 n) (p n) (q n)
  calc
    squaredPermutationEnergy (f n) (p n) /
        Fintype.card (V n) ≤
      (squaredPermutationEnergy (f n) (q n) +
        (hammingDist (fun x => p n x) (fun x => q n x) : ℝ)) /
          Fintype.card (V n) :=
      div_le_div_of_nonneg_right he (Nat.cast_nonneg _)
    _ = squaredPermutationEnergy (f n) (q n) /
          Fintype.card (V n) +
        SoficGroups.normalizedHamming (p n) (q n) := by
      rw [add_div]
      rfl
end SoficGroups.KunPositiveWordMidrankEnergy
