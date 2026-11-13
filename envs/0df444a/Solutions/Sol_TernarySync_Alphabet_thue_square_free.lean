-- Prove2me | solution 1 for TernarySync.Alphabet.thue_square_free
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:13:25.81271+00:00
-- url     : https://prove2.me/submissions/d0270afe-271c-4c3c-a1a5-a8f364a32f52

import Mathlib
import Definitions.Def_TernarySync_Alphabet_SyncString

section
set_option autoImplicit false

namespace TernarySync.Dev.Thue

/-- Thue–Morse word: parity of the binary digit sum. -/
def tm (n : ℕ) : Bool :=
  if h : n = 0 then false else if n % 2 = 0 then tm (n / 2) else !tm (n / 2)
termination_by n
decreasing_by all_goals omega

theorem tm_even (n : ℕ) : tm (2 * n) = tm n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [tm]
  · rw [tm]
    have h1 : ¬ (2 * n = 0) := by omega
    have h2 : 2 * n % 2 = 0 := by omega
    have h3 : 2 * n / 2 = n := by omega
    simp [h1, h2, h3]

theorem tm_odd (n : ℕ) : tm (2 * n + 1) = !tm n := by
  rw [tm]
  have h1 : ¬ (2 * n + 1 = 0) := by omega
  have h2 : ¬ (2 * n + 1 % 2 = 0) := by omega
  have h2' : (2 * n + 1) % 2 = 1 := by omega
  have h3 : (2 * n + 1) / 2 = n := by omega
  simp [h2', h3]

theorem tm_adj_even (m : ℕ) (hm : m % 2 = 0) : tm m ≠ tm (m + 1) := by
  obtain ⟨a, rfl⟩ : ∃ a, m = 2 * a := ⟨m / 2, by omega⟩
  rw [tm_even, tm_odd]
  cases tm a <;> simp

theorem alt_aux (i p : ℕ) (h : ∀ m, i ≤ m → m < i + p → tm m ≠ tm (m + 1)) :
    ∀ k, k ≤ p → tm (i + k) = (tm i ^^ decide (k % 2 = 1)) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 := h (i + k) (by omega) (by omega)
    have : tm (i + (k + 1)) = !tm (i + k) := by
      rw [← add_assoc]
      revert h2
      generalize tm (i + k + 1) = x
      generalize tm (i + k) = y
      cases x <;> cases y <;> simp
    rw [this, h1]
    rcases Nat.mod_two_eq_zero_or_one k with hk2 | hk2
    · have : (k + 1) % 2 = 1 := by omega
      simp [hk2, this]
    · have : ¬ ((k + 1) % 2 = 1) := by omega
      simp [hk2, this]

theorem no_overlap : ∀ p, 1 ≤ p → ∀ i, ¬ (∀ k, k ≤ p → tm (i + k) = tm (i + p + k)) := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hp i H
    rcases Nat.mod_two_eq_zero_or_one p with hp2 | hp2
    · obtain ⟨q, rfl⟩ : ∃ q, p = 2 * q := ⟨p / 2, by omega⟩
      have hq : 1 ≤ q := by omega
      obtain ⟨a, r, hr, rfl⟩ : ∃ a r, r < 2 ∧ i = 2 * a + r := ⟨i / 2, i % 2, by omega, by omega⟩
      refine ih q (by omega) hq a ?_
      intro k hk
      have := H (2 * k) (by omega)
      have e1 : 2 * a + r + 2 * k = 2 * (a + k) + r := by ring
      have e2 : 2 * a + r + 2 * q + 2 * k = 2 * (a + q + k) + r := by ring
      rw [e1, e2] at this
      rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl
      · simp only [add_zero, tm_even] at this
        rw [show a + k = a + k from rfl] at this
        simpa [add_assoc] using this
      · rw [tm_odd, tm_odd] at this
        simpa [add_assoc] using this
    · -- odd period: all adjacent pairs differ on [i, i+p]
      have hadj : ∀ m, i ≤ m → m < i + p → tm m ≠ tm (m + 1) := by
        intro m h1 h2
        rcases Nat.mod_two_eq_zero_or_one m with hm | hm
        · exact tm_adj_even m hm
        · have e1 := H (m - i) (by omega)
          have e2 := H (m - i + 1) (by omega)
          have a1 : i + (m - i) = m := by omega
          have a2 : i + p + (m - i) = m + p := by omega
          have a3 : i + (m - i + 1) = m + 1 := by omega
          have a4 : i + p + (m - i + 1) = m + 1 + p := by omega
          rw [a1, a2] at e1
          rw [a3, a4] at e2
          have := tm_adj_even (m + p) (by omega)
          rw [show m + p + 1 = m + 1 + p by omega, ← e1, ← e2] at this
          exact this
      have h0 := alt_aux i p hadj p le_rfl
      have h1 := H 0 (by omega)
      simp only [add_zero] at h1
      rw [h0] at h1
      have : decide (p % 2 = 1) = true := decide_eq_true hp2
      rw [this] at h1
      revert h1
      generalize tm i = x
      cases x <;> decide

def b (m : ℕ) : ℤ := if tm m then 1 else 0

theorem b_cases (m : ℕ) : b m = 0 ∨ b m = 1 := by
  unfold b; split_ifs <;> simp

theorem b_inj {m n : ℕ} (h : b m = b n) : tm m = tm n := by
  unfold b at h
  cases h1 : tm m <;> cases h2 : tm n <;> simp_all

def u (m : ℕ) : ℕ :=
  if tm (m + 1) then (if tm m then 1 else 2) else (if tm m then 0 else 1)

theorem u_lt (m : ℕ) : u m < 3 := by unfold u; split_ifs <;> omega

theorem u_eq (m : ℕ) : (u m : ℤ) = b (m + 1) - b m + 1 := by
  unfold u b; split_ifs <;> simp

def v (m : ℕ) : Fin 3 := ⟨u m, u_lt m⟩

theorem no_square_aux (i p : ℕ) (hp : 1 ≤ p) (h : ∀ k, k < p → v (i + k) = v (i + p + k)) : False := by
  have hu : ∀ k, k < p → (u (i + k) : ℤ) = u (i + p + k) := by
    intro k hk
    have := congrArg Fin.val (h k hk)
    simpa [v] using this
  have hE : ∀ k, k ≤ p → b (i + k + p) - b (i + k) = b (i + p) - b i := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := hu k (by omega)
      have h3 := u_eq (i + k)
      have h4 := u_eq (i + p + k)
      rw [show i + (k + 1) + p = i + p + k + 1 by omega, show i + (k + 1) = i + k + 1 by omega]
      rw [show i + k + p = i + p + k by omega] at h1
      omega
  have bi := b_cases i
  have bp := b_cases (i + p)
  have bpp := b_cases (i + p + p)
  have e0 := hE 0 (by omega)
  have ep := hE p le_rfl
  simp only [add_zero] at e0
  rcases (by omega : b (i + p) - b i = 0 ∨ b (i + p) - b i = 1 ∨ b (i + p) - b i = -1) with hz | hz | hz
  · refine no_overlap p hp i ?_
    intro k hk
    have := hE k hk
    rw [hz, show i + k + p = i + p + k by omega] at this
    exact b_inj (by omega)
  · omega
  · omega

end TernarySync.Dev.Thue

namespace TernarySync.Alphabet
open TernarySync.Dev.Thue in
theorem chk_thue_square_free (n : ℕ) :
    ∃ S : List (Fin 3), S.length = n ∧ IsSquareFree S := by
  refine ⟨(List.range n).map v, by simp, ?_⟩
  intro w hw ⟨X, hX, hwX⟩
  subst hwX
  obtain ⟨s, t, hst⟩ := hw
  have hlen : s.length + (X.length + X.length) + t.length = n := by
    have := congrArg List.length hst
    simp only [List.length_append, List.length_map, List.length_range] at this
    omega
  have hXpos : 1 ≤ X.length := List.length_pos_iff.mpr hX
  refine no_square_aux s.length X.length hXpos ?_
  intro k hk
  have hget : ∀ m, m < n → ((s ++ (X ++ X) ++ t)[m]? : Option (Fin 3)) = some (v m) := by
    intro m hm
    rw [hst]
    simp [hm]
  have g1 := hget (s.length + k) (by omega)
  have g2 := hget (s.length + X.length + k) (by omega)
  have c1 : (s ++ (X ++ X) ++ t)[s.length + k]? = X[k]? := by
    rw [List.append_assoc, List.getElem?_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rw [List.getElem?_append_left (by simp; omega)]
    rw [List.getElem?_append_left (by omega)]
  have c2 : (s ++ (X ++ X) ++ t)[s.length + X.length + k]? = X[k]? := by
    rw [List.append_assoc, List.getElem?_append_right (by omega)]
    rw [show s.length + X.length + k - s.length = X.length + k by omega]
    rw [List.getElem?_append_left (by simp; omega)]
    rw [List.getElem?_append_right (by omega)]
    rw [show X.length + k - X.length = k by omega]
  rw [c1] at g1
  rw [c2] at g2
  rw [g1] at g2
  exact Option.some.inj g2
end TernarySync.Alphabet
end

theorem solution : type_of% @TernarySync.Alphabet.chk_thue_square_free := @TernarySync.Alphabet.chk_thue_square_free
