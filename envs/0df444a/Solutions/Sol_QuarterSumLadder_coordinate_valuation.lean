-- Prove2me | solution 1 for QuarterSumLadder.coordinate_valuation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:04:14.49004+00:00
-- url     : https://prove2.me/submissions/e3e42ddd-a1fc-48c7-a304-8dd0c2275d06

module
public import Mathlib
public import Definitions.Def_QuarterSumLadder_Arith
public import Theorems.Thm_QuarterSumLadder_sq_add_sq_odd
public import Theorems.Thm_QuarterSumLadder_sq_add_sq_mixed
public import Theorems.Thm_QuarterSumLadder_padicValInt_two_mul
public import Theorems.Thm_QuarterSumLadder_padicValInt_odd

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
namespace QuarterSumLadder
theorem _root_.solution {x y : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) :
    padicValInt 2 (x ^ 2 + y ^ 2) =
      2 * min (padicValInt 2 x) (padicValInt 2 y) +
        if padicValInt 2 x = padicValInt 2 y then 1 else 0 := by
  induction h : x.natAbs using Nat.strong_induction_on generalizing x y with
  | _ n ih =>
    rcases Int.emod_two_eq_zero_or_one x with hx2 | hx2 <;>
      rcases Int.emod_two_eq_zero_or_one y with hy2 | hy2
    · obtain ⟨a, rfl⟩ : ∃ a, x = 2 * a := ⟨x / 2, by omega⟩
      obtain ⟨b, rfl⟩ : ∃ b, y = 2 * b := ⟨y / 2, by omega⟩
      have ha : a ≠ 0 := by rintro rfl; simp at hx
      have hb : b ≠ 0 := by rintro rfl; simp at hy
      have hlt : a.natAbs < n := by rw [← h, Int.natAbs_mul]; have := Int.natAbs_pos.2 ha; simp; omega
      have hN : (2 * a) ^ 2 + (2 * b) ^ 2 = 2 * (2 * (a ^ 2 + b ^ 2)) := by ring
      have hab : a ^ 2 + b ^ 2 ≠ 0 := by positivity
      rw [hN, padicValInt_two_mul (by positivity), padicValInt_two_mul hab, ih _ hlt ha hb rfl,
        padicValInt_two_mul ha, padicValInt_two_mul hb]
      simp only [add_left_inj]
      rw [min_add_add_right]; ring_nf
    · rw [padicValInt_odd hy2]
      have hv : 1 ≤ padicValInt 2 x := by
        obtain ⟨a, rfl⟩ : ∃ a, x = 2 * a := ⟨x / 2, by omega⟩
        rw [padicValInt_two_mul (by rintro rfl; simp at hx)]; omega
      have := sq_add_sq_mixed (x := y) (y := x) hy2 hx2
      rw [add_comm, padicValInt_odd this, if_neg (by omega)]; simp
    · rw [padicValInt_odd hx2]
      have hv : 1 ≤ padicValInt 2 y := by
        obtain ⟨b, rfl⟩ : ∃ b, y = 2 * b := ⟨y / 2, by omega⟩
        rw [padicValInt_two_mul (by rintro rfl; simp at hy)]; omega
      have := sq_add_sq_mixed hx2 hy2
      rw [padicValInt_odd this, if_neg (by omega)]; simp
    · rw [padicValInt_odd hx2, padicValInt_odd hy2, if_pos rfl]
      have h8 := sq_add_sq_odd hx2 hy2
      obtain ⟨m, hm⟩ : ∃ m, x ^ 2 + y ^ 2 = 2 * m ∧ m % 2 = 1 := ⟨(x ^ 2 + y ^ 2) / 2, by omega⟩
      rw [hm.1, padicValInt_two_mul (by omega), padicValInt_odd hm.2]; simp
end QuarterSumLadder
