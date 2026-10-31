-- Prove2me | solution 1 for OddGoldbach19.small_count_A
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-30T16:07:56.876743+00:00
-- url     : https://prove2.me/submissions/331fdc3d-3ebc-44e3-82d9-5eaa163bb5e9

import Definitions.Def_Schnir_defs
import Mathlib

set_option autoImplicit false
open Finset

namespace OddGoldbach19

/-- A finite set with no three consecutive elements gains at least half its size after a unit shift. -/
theorem three_card_le_two_card_union_shift (X : Finset ℕ)
    (hno : ∀ x ∈ X, ¬ (x + 1 ∈ X ∧ x + 2 ∈ X)) :
    3 * X.card ≤ 2 * (X ∪ X.image (fun x => x + 1)).card := by
  classical
  let Z := X.filter (fun x => x + 1 ∈ X)
  have hinj : Function.Injective (fun x : ℕ => x + 1) := by intro x y h; dsimp at h; omega
  have hcard : (Z.image (fun x => x + 1)).card = Z.card := card_image_of_injective Z hinj
  have hdis : Disjoint Z (Z.image (fun x => x + 1)) := by
    apply disjoint_left.2
    intro x hx hy
    obtain ⟨y, hy, hxy⟩ := mem_image.1 hy
    have hx' := mem_filter.1 hx
    have hy' := mem_filter.1 hy
    apply hno y hy'.1
    constructor
    · exact hy'.2
    · have he : y + 2 = x + 1 := by omega
      rw [he]
      exact hx'.2
  have hsub : Z ∪ Z.image (fun x => x + 1) ⊆ X := by
    intro x hx
    rcases mem_union.1 hx with hx | hx
    · exact (mem_filter.1 hx).1
    · obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
      exact (mem_filter.1 hy).2
  have hsmall := card_le_card hsub
  rw [card_union_of_disjoint hdis, hcard] at hsmall
  have hinter : X ∩ X.image (fun x => x + 1) = Z.image (fun x => x + 1) := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := mem_image.1 (mem_inter.1 hx).2
      exact mem_image.2 ⟨y, mem_filter.2 ⟨hy, (mem_inter.1 hx).1⟩, rfl⟩
    · intro hx
      obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
      exact mem_inter.2 ⟨(mem_filter.1 hy).2,
        mem_image.2 ⟨y, (mem_filter.1 hy).1, rfl⟩⟩
  have hu := card_union_add_card_inter X (X.image (fun x => x + 1))
  rw [hinter, hcard, card_image_of_injective X hinj] at hu
  omega

/-- Three consecutive odd numbers at least 11 cannot all be prime. -/
theorem no_three_shifted_odd_primes (x : ℕ) :
    ¬ (Nat.Prime (2 * x + 11) ∧ Nat.Prime (2 * (x + 1) + 11) ∧
      Nat.Prime (2 * (x + 2) + 11)) := by
  rintro ⟨h0, h1, h2⟩
  have hmod (n : ℕ) (hn : 11 ≤ n) (hp : Nat.Prime n) : n % 3 ≠ 0 := by
    intro hm
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.dvd_of_mod_eq_zero hm)
    omega
  have hm0 := hmod _ (by omega) h0
  have hm1 := hmod _ (by omega) h1
  have hm2 := hmod _ (by omega) h2
  have hx : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
  rcases hx with h | h | h
  all_goals simp_all [Nat.add_mod, Nat.mul_mod]

/-- The 3/2 counting gain used by Riesel--Vaughan's small-range argument (p. 58). -/
theorem prime_shift_union_count (N : ℕ) :
    3 * ((range N).filter (fun x => Nat.Prime (2 * x + 11))).card ≤
      2 * (((range N).filter (fun x => Nat.Prime (2 * x + 11))) ∪
        ((range N).filter (fun x => Nat.Prime (2 * x + 11))).image (fun x => x + 1)).card := by
  apply three_card_le_two_card_union_shift
  intro x hx hnext
  exact no_three_shifted_odd_primes x ⟨(mem_filter.1 hx).2,
    (mem_filter.1 hnext.1).2, (mem_filter.1 hnext.2).2⟩

#print axioms prime_shift_union_count
end OddGoldbach19


set_option autoImplicit false
open Finset
open scoped Pointwise

open OddGoldbach19

open Classical in
/-- An explicit 3/2 prime-counting lower bound for the shared additive set A. -/
theorem solution (N : ℕ) (hN : 5 ≤ N) :
    3 * Nat.primeCounting (2 * N + 1) ≤
      2 * ((Ioc 0 N).filter (fun a => a ∈ Schnir.A)).card + 12 := by
  classical
  let X := (range (N - 4)).filter (fun x => Nat.Prime (2 * x + 11))
  let P := (range (2 * N + 2)).filter Nat.Prime
  have hpi : P.card = Nat.primeCounting (2 * N + 1) := by
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have hinj : Function.Injective (fun x : ℕ => 2 * x + 11) := by
    intro x y h; dsimp at h; omega
  have hP : P ⊆ X.image (fun x => 2 * x + 11) ∪ {2, 3, 5, 7} := by
    intro q hq
    have hq' : q < 2 * N + 2 ∧ q.Prime := by simpa [P] using hq
    apply mem_union.2
    by_cases hsmall : q < 11
    · right
      interval_cases q <;> norm_num at hq' <;> norm_num
    · left
      have h11 : 11 ≤ q := by omega
      have hodd := Nat.odd_iff.1 (hq'.2.odd_of_ne_two (by omega))
      refine mem_image.2 ⟨(q - 11) / 2, ?_, ?_⟩
      · apply mem_filter.2
        constructor
        · apply mem_range.2; omega
        · convert hq'.2 using 1 <;> omega
      · omega
  have hpc : Nat.primeCounting (2 * N + 1) ≤ X.card + 4 := by
    have h := (card_le_card hP).trans (card_union_le _ _)
    rw [card_image_of_injective X hinj, hpi] at h
    norm_num at h
    exact h
  let U := X ∪ X.image (fun x => x + 1)
  have hU : 3 * X.card ≤ 2 * U.card := prime_shift_union_count (N - 4)
  have hinj4 : Function.Injective (fun x : ℕ => x + 4) := by
    intro x y h; dsimp at h; omega
  have hsub : U.image (fun x => x + 4) ⊆ (Ioc 0 N).filter (fun a => a ∈ Schnir.A) := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := mem_image.1 ha
    change x ∈ X ∪ X.image (fun x => x + 1) at hx
    rcases mem_union.1 hx with hx | hx
    · have hx' : x < N - 4 ∧ Nat.Prime (2 * x + 11) := by simpa [X] using hx
      apply mem_filter.2
      refine ⟨mem_Ioc.2 ⟨by omega, by omega⟩, ?_⟩
      apply Set.mem_add.2
      refine ⟨x + 4, ?_, 0, ?_, by omega⟩
      · exact ⟨2 * x + 11, hx'.2, by omega, by omega⟩
      · exact ⟨3, Nat.prime_three, by norm_num, rfl⟩
    · obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
      have hy' : y < N - 4 ∧ Nat.Prime (2 * y + 11) := by simpa [X] using hy
      apply mem_filter.2
      refine ⟨mem_Ioc.2 ⟨by omega, by omega⟩, ?_⟩
      apply Set.mem_add.2
      refine ⟨y + 4, ?_, 1, ?_, by omega⟩
      · exact ⟨2 * y + 11, hy'.2, by omega, by omega⟩
      · exact ⟨5, by norm_num, by norm_num, rfl⟩
  have hc := card_le_card hsub
  rw [card_image_of_injective U hinj4] at hc
  omega

#print axioms solution

