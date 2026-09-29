-- Prove2me | solution 1 for WittVector.exists_eq_sum_iterate_verschiebung_teichmuller_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/466335ae-e738-5844-914c-c7ea642e856d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WittVector_exists_eq_sum_iterate_verschiebung_teichmuller_add

set_option autoImplicit false

namespace WTESol

open WittVector

variable {p : ℕ} [hp : Fact p.Prime] {B : Type} [CommRing B]

theorem coeff_iterate_V_teichmuller (n k : ℕ) (a : B) :
    ((⇑(verschiebung : WittVector p B →+ WittVector p B))^[n] (teichmuller p a)).coeff k = if k = n then a else 0 := by
  split_ifs with h
  · subst h
    have := iterate_verschiebung_coeff (p := p) (teichmuller p a) k 0
    rw [zero_add] at this
    rw [this, teichmuller_coeff_zero]
  · rcases lt_or_gt_of_ne h with hlt | hgt
    · exact iterate_verschiebung_coeff_eq_zero _ hlt
    · obtain ⟨d, rfl⟩ : ∃ d, k = (d + 1) + n := ⟨k - n - 1, by omega⟩
      rw [iterate_verschiebung_coeff]
      exact teichmuller_coeff_pos p a _ (Nat.succ_pos d)

theorem coeff_partial (w : WittVector p B) (N : ℕ) : ∀ k : ℕ,
    (∑ n ∈ Finset.range N, (⇑(verschiebung : WittVector p B →+ WittVector p B))^[n] (teichmuller p (w.coeff n))).coeff k = if k < N then w.coeff k else 0 := by
  induction N with
  | zero => intro k; simp
  | succ N ih =>
    intro k
    rw [Finset.sum_range_succ, coeff_add_of_disjoint, ih, coeff_iterate_V_teichmuller]
    · by_cases h1 : k < N
      · rw [if_pos h1, if_neg (by omega), if_pos (by omega), add_zero]
      · by_cases h2 : k = N
        · subst h2; rw [if_neg h1, if_pos rfl, if_pos (Nat.lt_succ_self _), zero_add]
        · rw [if_neg h1, if_neg h2, if_neg (by omega), add_zero]
    · intro n
      rw [ih, coeff_iterate_V_teichmuller]
      by_cases h : n < N
      · right; rw [if_neg (by omega)]
      · left; rw [if_neg h]

theorem coeff_tail (w : WittVector p B) (N k : ℕ) :
    ((⇑(verschiebung : WittVector p B →+ WittVector p B))^[N] (w.shift N)).coeff k = if N ≤ k then w.coeff k else 0 := by
  split_ifs with h
  · obtain ⟨d, rfl⟩ : ∃ d, k = d + N := ⟨k - N, by omega⟩
    rw [iterate_verschiebung_coeff, shift_coeff, add_comm]
  · exact iterate_verschiebung_coeff_eq_zero _ (by omega)

theorem expansion (w : WittVector p B) (N : ℕ) :
    w = (∑ n ∈ Finset.range N, (⇑(verschiebung : WittVector p B →+ WittVector p B))^[n] (teichmuller p (w.coeff n))) + (⇑(verschiebung : WittVector p B →+ WittVector p B))^[N] (w.shift N) := by
  ext k
  rw [coeff_add_of_disjoint, coeff_partial, coeff_tail]
  · by_cases h : k < N
    · rw [if_pos h, if_neg (by omega), add_zero]
    · rw [if_neg h, if_pos (by omega), zero_add]
  · intro n
    rw [coeff_partial, coeff_tail]
    by_cases h : n < N
    · right; rw [if_neg (by omega)]
    · left; rw [if_neg h]

end WTESol

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (w : WittVector p B) (N : ℕ) :
    ∃ w' : WittVector p B,
      w = (∑ n ∈ Finset.range N, (⇑(WittVector.verschiebung : WittVector p B →+ WittVector p B))^[n]
            (WittVector.teichmuller p (w.coeff n))) +
          (⇑(WittVector.verschiebung : WittVector p B →+ WittVector p B))^[N] w' :=
  ⟨w.shift N, WTESol.expansion w N⟩

end S_WittVector_exists_eq_sum_iterate_verschiebung_teichmuller_add
end P2MW
export P2MW.S_WittVector_exists_eq_sum_iterate_verschiebung_teichmuller_add (solution)
