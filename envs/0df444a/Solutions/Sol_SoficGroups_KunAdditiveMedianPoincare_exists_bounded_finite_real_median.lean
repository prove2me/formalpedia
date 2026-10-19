-- Prove2me | solution 1 for SoficGroups.KunAdditiveMedianPoincare.exists_bounded_finite_real_median
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/79342f3a-01e4-472b-a1ae-73e95085f1e8

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_CheegerPoincare_exists_finite_real_median

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunAdditiveMedianPoincare
open SoficGroups.CheegerPoincare
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunAdditiveMedianPoincare
theorem _root_.solution
    {V : Type*} [Fintype V] [Nonempty V]
    (f : V → ℝ)
    (hf : ∀ x, 0 ≤ f x)
    (hf_one : ∀ x, f x ≤ 1) :
    ∃ m : ℝ, 0 ≤ m ∧ m ≤ 1 ∧
      2 * (SoficGroups.CheegerPoincare.lowerLevel f m).card ≤
          Fintype.card V ∧
      2 * (SoficGroups.CheegerPoincare.upperLevel f m).card ≤
          Fintype.card V := by
  classical
  obtain ⟨m, hbelow, habove⟩ :=
    SoficGroups.CheegerPoincare.exists_finite_real_median f
  have hcard : 0 < Fintype.card V := Fintype.card_pos_iff.mpr
    (inferInstance : Nonempty V)
  have hm_nonnegative : 0 ≤ m := by
    by_contra hnot
    have hm_negative : m < 0 := lt_of_not_ge hnot
    have hupper :
        SoficGroups.CheegerPoincare.upperLevel f m =
          (Finset.univ : Finset V) := by
      ext x
      simp only [SoficGroups.CheegerPoincare.mem_upperLevel,
        Finset.mem_univ, iff_true]
      exact hm_negative.trans_le (hf x)
    rw [hupper, Finset.card_univ] at habove
    omega
  have hm_one : m ≤ 1 := by
    by_contra hnot
    have hm_greater : 1 < m := lt_of_not_ge hnot
    have hlower :
        SoficGroups.CheegerPoincare.lowerLevel f m =
          (Finset.univ : Finset V) := by
      ext x
      simp only [SoficGroups.CheegerPoincare.mem_lowerLevel,
        Finset.mem_univ, iff_true]
      exact (hf_one x).trans_lt hm_greater
    rw [hlower, Finset.card_univ] at hbelow
    omega
  exact ⟨m, hm_nonnegative, hm_one, hbelow, habove⟩
end SoficGroups.KunAdditiveMedianPoincare
