-- Prove2me | solution 1 for Subgroup.card_quotient_zpowers_le_three_of_injective_of_sq_sub_mul_add_one_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/26049891-d5d1-5f7d-9287-da7c8e3f61e7

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subgroup_card_quotient_zpowers_le_three_of_injective_of_sq_sub_mul_add_one_eq_zero

set_option autoImplicit false

namespace CornersGroupTr

variable {M : ℕ} {H : Type*} [CommGroup H] (c : H) (χ : H →* (ZMod M)ˣ)

abbrev sc : H →* ZMod M := (Units.coeHom (ZMod M)).comp χ

theorem sc_apply (h : H) : sc χ h = ((χ h : (ZMod M)ˣ) : ZMod M) := rfl

variable (hχ : Function.Injective χ) (hc : sc χ c = -1) (hM : 3 ≤ M)
  (htr : ∀ h : H, ∃ t : ℤ, (t = -2 ∨ t = -1 ∨ t = 0 ∨ t = 1 ∨ t = 2) ∧
      (sc χ h) ^ 2 - (t : ZMod M) * (sc χ h) + 1 = 0 ∧ (t = 2 → h = 1) ∧ (t = -2 → h = c))

section Basic

include hχ in
theorem eq_of_sc_eq {a b : H} (h : sc χ a = sc χ b) : a = b := hχ (Units.ext h)

include hχ in
theorem pow_eq_of_sc {a b : H} {n : ℕ} (h : (sc χ a) ^ n = sc χ b) : a ^ n = b :=
  eq_of_sc_eq χ hχ (by rw [map_pow]; exact h)

include hM in
theorem two_ne_zero' : (2 : ZMod M) ≠ 0 := by
  intro h2
  have : (2 : ZMod M) = ((2 : ℕ) : ZMod M) := by norm_cast
  rw [this, ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd two_pos h2
  omega

include hM in
theorem eq_three_of_three_eq_zero (h3 : (3 : ZMod M) = 0) : M = 3 := by
  have : (3 : ZMod M) = ((3 : ℕ) : ZMod M) := by norm_cast
  rw [this, ZMod.natCast_eq_zero_iff] at h3
  have := Nat.le_of_dvd (by norm_num) h3
  omega

include hχ hc in
theorem c_sq : c * c = 1 := by
  apply eq_of_sc_eq χ hχ
  rw [map_mul, hc, map_one]; ring

include hc hM in
theorem c_ne_one : c ≠ 1 := by
  intro h
  rw [h, map_one] at hc
  exact two_ne_zero' hM (by linear_combination hc)

include hχ hc htr in

theorem classify (h : H) :
    h = 1 ∨ h = c ∨ (h ^ 4 = 1 ∧ (sc χ h) ^ 2 + 1 = 0) ∨
      (h ^ 3 = 1 ∧ (sc χ h) ^ 2 + (sc χ h) + 1 = 0) ∨ (h ^ 3 = c ∧ (sc χ h) ^ 2 - (sc χ h) + 1 = 0) := by
  obtain ⟨t, ht, rel, h2, hm2⟩ := htr h
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inl (hm2 rfl))
  · push_cast at rel
    have r : (sc χ h) ^ 2 + (sc χ h) + 1 = 0 := by linear_combination rel
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, r⟩)))
    apply pow_eq_of_sc χ hχ
    rw [map_one]
    linear_combination (sc χ h - 1) * r
  · push_cast at rel
    have r : (sc χ h) ^ 2 + 1 = 0 := by linear_combination rel
    refine Or.inr (Or.inr (Or.inl ⟨?_, r⟩))
    apply pow_eq_of_sc χ hχ
    rw [map_one]
    linear_combination ((sc χ h) ^ 2 - 1) * r
  · push_cast at rel
    have r : (sc χ h) ^ 2 - (sc χ h) + 1 = 0 := by linear_combination rel
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, r⟩)))
    apply pow_eq_of_sc χ hχ
    rw [hc]
    linear_combination (sc χ h + 1) * r
  · exact Or.inl (h2 rfl)

include hχ hc hM htr in

theorem eq_one_or_eq_c_of_sq {h : H} (h2 : h * h = 1) : h = 1 ∨ h = c := by
  rcases classify c χ hχ hc htr h with e | e | ⟨-, r⟩ | ⟨h3, -⟩ | ⟨h3, -⟩
  · exact Or.inl e
  · exact Or.inr e
  · exfalso
    have hsq : (sc χ h) ^ 2 = 1 := by rw [← map_pow, pow_two, h2, map_one]
    exact two_ne_zero' hM (by linear_combination r - hsq)
  · left; rwa [pow_three, h2, mul_one] at h3
  · right; rwa [pow_three, h2, mul_one] at h3

include hχ hc htr in
theorem pow_four_or_pow_six (h : H) : h ^ 4 = 1 ∨ h ^ 6 = 1 := by
  rcases classify c χ hχ hc htr h with rfl | e | ⟨h4, -⟩ | ⟨h3, -⟩ | ⟨h3, -⟩
  · exact Or.inl (one_pow 4)
  · left
    rw [e, show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, pow_two c, c_sq c χ hχ hc, one_pow]
  · exact Or.inl h4
  · right; rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, h3, one_pow]
  · right; rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, h3, pow_two, c_sq c χ hχ hc]

include hχ hc htr in

theorem sq_eq_neg_one {h : H} (h4 : h ^ 4 = 1) (h1 : h ≠ 1) (h2 : h ≠ c) : (sc χ h) ^ 2 + 1 = 0 := by
  rcases classify c χ hχ hc htr h with e | e | ⟨-, r⟩ | ⟨h3, -⟩ | ⟨h3, -⟩
  · exact absurd e h1
  · exact absurd e h2
  · exact r
  · exfalso; apply h1
    have e : h ^ 4 = h ^ 3 * h := by group
    rw [e, h3, one_mul] at h4; exact h4
  · exfalso; apply h2
    have e : h ^ 4 = h ^ 3 * h := by group
    rw [e, h3] at h4
    have : h = c⁻¹ := eq_inv_of_mul_eq_one_right h4
    rw [this, inv_eq_iff_mul_eq_one, c_sq c χ hχ hc]

include hχ hc hM htr in

theorem cube (h : H) (h6 : h ^ 6 = 1) (h1 : h ≠ 1) (h2 : h ≠ c) :
    (h ^ 3 = 1 ∧ (sc χ h) ^ 2 + (sc χ h) + 1 = 0) ∨ (h ^ 3 = c ∧ (sc χ h) ^ 2 - (sc χ h) + 1 = 0) := by
  rcases classify c χ hχ hc htr h with e | e | ⟨h4, -⟩ | e | e
  · exact absurd e h1
  · exact absurd e h2
  · exfalso
    have hsq : h * h = 1 := by
      have e : h ^ 6 = h ^ 4 * (h * h) := by group
      rw [e, h4, one_mul] at h6; exact h6
    rcases eq_one_or_eq_c_of_sq c χ hχ hc hM htr hsq with e | e
    · exact h1 e
    · exact h2 e
  · exact Or.inl e
  · exact Or.inr e

end Basic

section Count

include hχ hc hM htr in

theorem sq_eq_c {h : H} (h4 : h ^ 4 = 1) (h1 : h ≠ 1) (h2 : h ≠ c) : h * h = c := by
  have : (h * h) * (h * h) = 1 := by
    have e : h ^ 4 = (h * h) * (h * h) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [← e]; exact h4
  rcases eq_one_or_eq_c_of_sq c χ hχ hc hM htr this with e | e
  · rcases eq_one_or_eq_c_of_sq c χ hχ hc hM htr e with e' | e'
    · exact absurd e' h1
    · exact absurd e' h2
  · exact e

include hχ hc hM htr in

theorem not_four_and_six {h k : H} (h4 : h ^ 4 = 1) (h1 : h ≠ 1) (h2 : h ≠ c) (k6 : k ^ 6 = 1) (k1 : k ≠ 1)
    (k2 : k ≠ c) : False := by
  rcases pow_four_or_pow_six c χ hχ hc htr (h * k) with e | e
  · have hk4 : k ^ 4 = 1 := by rw [mul_pow, h4, one_mul] at e; exact e
    have hk2 : k * k = 1 := by
      have : k ^ 6 = k ^ 4 * (k * k) := by group
      rw [this, hk4, one_mul] at k6; exact k6
    rcases eq_one_or_eq_c_of_sq c χ hχ hc hM htr hk2 with e' | e'
    · exact k1 e'
    · exact k2 e'
  · have hh6 : h ^ 6 = 1 := by rw [mul_pow, k6, mul_one] at e; exact e
    have hh2 : h * h = 1 := by
      have : h ^ 6 = h ^ 4 * (h * h) := by group
      rw [this, h4, one_mul] at hh6; exact hh6
    rcases eq_one_or_eq_c_of_sq c χ hχ hc hM htr hh2 with e' | e'
    · exact h1 e'
    · exact h2 e'

include hχ hc hM htr in

theorem four_mem {h k : H} (h4 : h ^ 4 = 1) (h1 : h ≠ 1) (h2 : h ≠ c) (k4 : k ^ 4 = 1) (k1 : k ≠ 1) (k2 : k ≠ c) :
    k = h ∨ k = c * h := by
  have eh := sq_eq_c c χ hχ hc hM htr h4 h1 h2
  have ek := sq_eq_c c χ hχ hc hM htr k4 k1 k2
  have hsq : (k * h⁻¹) * (k * h⁻¹) = 1 := by
    rw [mul_mul_mul_comm, ← mul_inv, eh, ek, mul_inv_cancel]
  rcases eq_one_or_eq_c_of_sq c χ hχ hc hM htr hsq with e | e
  · left; rwa [mul_inv_eq_one] at e
  · right; rwa [mul_inv_eq_iff_eq_mul] at e

include hχ hc hM in
theorem ne_c_of_cube {g : H} (g3 : g ^ 3 = 1) : g ≠ c := by
  intro gc
  rw [gc] at g3
  rw [pow_three, c_sq c χ hχ hc, mul_one] at g3
  exact c_ne_one c χ hc hM g3

include hχ hc hM htr in
theorem root_of_cube {g : H} (g3 : g ^ 3 = 1) (g1 : g ≠ 1) : (sc χ g) ^ 2 + (sc χ g) + 1 = 0 := by
  have g6 : g ^ 6 = 1 := by rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, g3, one_pow]
  rcases cube c χ hχ hc hM htr g g6 g1 (ne_c_of_cube c χ hχ hc hM g3) with ⟨-, e⟩ | ⟨e3, -⟩
  · exact e
  · exact absurd (e3.symm.trans g3) (c_ne_one c χ hc hM)

include hχ hc hM htr in

theorem three_ne_zero_of_cube {g : H} (g3 : g ^ 3 = 1) (g1 : g ≠ 1) : (3 : ZMod M) ≠ 0 := by
  intro h3
  have r := root_of_cube c χ hχ hc hM htr g3 g1
  obtain rfl := eq_three_of_three_eq_zero hM h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsq : (sc χ g - 1) ^ 2 = 0 := by linear_combination r - (sc χ g) * h3
  have h0 : sc χ g - 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hsq
  apply g1
  apply eq_of_sc_eq χ hχ
  rw [map_one]
  linear_combination h0

include hχ hc hM htr in

theorem three_mem {h k : H} (h3 : h ^ 3 = 1) (h1 : h ≠ 1) (k3 : k ^ 3 = 1) (k1 : k ≠ 1) :
    k = h ∨ k = h * h := by
  have rh := root_of_cube c χ hχ hc hM htr h3 h1
  have rk := root_of_cube c χ hχ hc hM htr k3 k1
  have l3 : (sc χ h) ^ 3 = 1 := by rw [← map_pow, h3, map_one]
  have m3 : (sc χ k) ^ 3 = 1 := by rw [← map_pow, k3, map_one]
  have h3ne := three_ne_zero_of_cube c χ hχ hc hM htr h3 h1
  by_contra hk
  push Not at hk
  have hμ1 : (sc χ k) ≠ (sc χ h) := fun e => hk.1 (eq_of_sc_eq χ hχ e)
  have hμ2 : (sc χ k) ≠ (sc χ h) ^ 2 := fun e =>
    hk.2 (eq_of_sc_eq χ hχ (by rw [map_mul, ← pow_two]; exact e))

  have prod : ∀ g : H, g ^ 3 = 1 → sc χ g = 1 ∨ (sc χ g) ^ 2 + (sc χ g) + 1 = 0 := by
    intro g g3
    by_cases g1 : g = 1
    · left; rw [g1, map_one]
    · right; exact root_of_cube c χ hχ hc hM htr g3 g1
  have hk3 : (h * k) ^ 3 = 1 := by rw [mul_pow, h3, k3, one_mul]
  have hkk3 : (h * (k * k)) ^ 3 = 1 := by
    have e : (h * (k * k)) ^ 3 = h ^ 3 * (k ^ 3) ^ 2 := by rw [mul_pow, ← pow_two, ← pow_mul, ← pow_mul]
    rw [e, h3, k3, one_pow, one_mul]
  have s1 : sc χ (h * k) = sc χ h * sc χ k := map_mul _ _ _
  have s2 : sc χ (h * (k * k)) = sc χ h * (sc χ k) ^ 2 := by rw [map_mul, map_mul, pow_two]
  rcases prod (h * k) hk3 with e | e
  ·
    apply hμ2
    rw [s1] at e
    linear_combination (sc χ h) ^ 2 * e - (sc χ k) * l3
  rcases prod (h * (k * k)) hkk3 with e' | e'
  ·
    apply hμ1
    rw [s2] at e'
    linear_combination (sc χ h) * m3 - (sc χ k) * e'
  ·
    rw [s1] at e
    rw [s2] at e'
    apply h3ne
    linear_combination e + e' - ((sc χ h) ^ 2 + (sc χ h) + 1) * rk + rh + rk - (sc χ h) ^ 2 * (sc χ k) * m3

end Count

section Final

include hχ hc hM htr in

theorem card_le_six [Fintype H] : Fintype.card H ≤ 6 := by
  classical
  have hc1 := c_ne_one c χ hc hM
  by_cases h3 : ∃ h₀ : H, h₀ ^ 3 = 1 ∧ h₀ ≠ 1
  · obtain ⟨h₀, h03, h01⟩ := h3
    have h0c := ne_c_of_cube c χ hχ hc hM h03
    have h06 : h₀ ^ 6 = 1 := by rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, h03, one_pow]
    let f : Fin 6 → H := ![1, c, h₀, h₀ * h₀, c * h₀, c * (h₀ * h₀)]
    refine (Fintype.card_le_of_surjective f fun x => ?_).trans (by simp)
    by_cases hx1 : x = 1
    · exact ⟨0, hx1.symm⟩
    by_cases hxc : x = c
    · exact ⟨1, hxc.symm⟩
    rcases pow_four_or_pow_six c χ hχ hc htr x with x4 | x6
    · exact (not_four_and_six c χ hχ hc hM htr x4 hx1 hxc h06 h01 h0c).elim
    rcases cube c χ hχ hc hM htr x x6 hx1 hxc with ⟨x3, -⟩ | ⟨x3, -⟩
    · rcases three_mem c χ hχ hc hM htr h03 h01 x3 hx1 with e | e
      · exact ⟨2, e.symm⟩
      · exact ⟨3, e.symm⟩
    · have y3 : (c * x) ^ 3 = 1 := by rw [mul_pow, x3, pow_three, c_sq c χ hχ hc, mul_one, c_sq c χ hχ hc]
      have y1 : c * x ≠ 1 := by
        intro e; apply hxc
        rw [← c_sq c χ hχ hc] at e
        exact mul_left_cancel e
      rcases three_mem c χ hχ hc hM htr h03 h01 y3 y1 with e | e
      · refine ⟨4, ?_⟩
        show c * h₀ = x
        rw [← e, ← mul_assoc, c_sq c χ hχ hc, one_mul]
      · refine ⟨5, ?_⟩
        show c * (h₀ * h₀) = x
        rw [← e, ← mul_assoc, c_sq c χ hχ hc, one_mul]
  · push Not at h3
    have no3 : ∀ x : H, x ≠ 1 → x ≠ c → x ^ 6 = 1 → False := by
      intro x hx1 hxc x6
      rcases cube c χ hχ hc hM htr x x6 hx1 hxc with ⟨x3, -⟩ | ⟨x3, -⟩
      · exact hx1 (h3 x x3)
      · have y3 : (c * x) ^ 3 = 1 := by rw [mul_pow, x3, pow_three, c_sq c χ hχ hc, mul_one, c_sq c χ hχ hc]
        have := h3 (c * x) y3
        apply hxc
        rw [← c_sq c χ hχ hc] at this
        exact mul_left_cancel this
    by_cases h4 : ∃ h₀ : H, h₀ ^ 4 = 1 ∧ h₀ ≠ 1 ∧ h₀ ≠ c
    · obtain ⟨h₀, h04, h01, h0c⟩ := h4
      let f : Fin 6 → H := ![1, c, h₀, c * h₀, 1, 1]
      refine (Fintype.card_le_of_surjective f fun x => ?_).trans (by simp)
      by_cases hx1 : x = 1
      · exact ⟨0, hx1.symm⟩
      by_cases hxc : x = c
      · exact ⟨1, hxc.symm⟩
      rcases pow_four_or_pow_six c χ hχ hc htr x with x4 | x6
      · rcases four_mem c χ hχ hc hM htr h04 h01 h0c x4 hx1 hxc with e | e
        · exact ⟨2, e.symm⟩
        · exact ⟨3, e.symm⟩
      · exact (no3 x hx1 hxc x6).elim
    · push Not at h4
      let f : Fin 6 → H := ![1, c, 1, 1, 1, 1]
      refine (Fintype.card_le_of_surjective f fun x => ?_).trans (by simp)
      by_cases hx1 : x = 1
      · exact ⟨0, hx1.symm⟩
      by_cases hxc : x = c
      · exact ⟨1, hxc.symm⟩
      rcases pow_four_or_pow_six c χ hχ hc htr x with x4 | x6
      · exact (hxc (h4 x x4 hx1)).elim
      · exact (no3 x hx1 hxc x6).elim

include hχ hc hM in
theorem orderOf_c : orderOf c = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact c_sq c χ hχ hc) (c_ne_one c χ hc hM)

include hχ hc hM in
theorem mem_zpowers_c [Finite H] {x : H} (hx : x ∈ Subgroup.zpowers c) : x = 1 ∨ x = c := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, orderOf_c c χ hχ hc hM] at hx
  simp only [Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  interval_cases i
  · left; rw [pow_zero]
  · right; rw [pow_one]

include hχ hc hM htr in
theorem card_quot_le_three [Finite H] : Nat.card (H ⧸ Subgroup.zpowers c) ≤ 3 := by
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers c)
  rw [Nat.card_zpowers, orderOf_c c χ hχ hc hM] at hcard
  have h6 : Nat.card H ≤ 6 := by
    have := Fintype.ofFinite H
    rw [Nat.card_eq_fintype_card]; exact card_le_six c χ hχ hc hM htr
  omega

end Final

end CornersGroupTr

open CornersGroupTr in

theorem solution
    (M : ℕ) (hM : 3 ≤ M) (H : Type*) [CommGroup H] [Finite H]
    (c : H) (hc2 : c * c = 1)
    (χ : H →* (ZMod M)ˣ) (hχ : Function.Injective χ) (hc : ((χ c : (ZMod M)ˣ) : ZMod M) = -1)
    (htr : ∀ h : H, ∃ t : ℤ, (t = -2 ∨ t = -1 ∨ t = 0 ∨ t = 1 ∨ t = 2) ∧
      ((χ h : (ZMod M)ˣ) : ZMod M) ^ 2 - (t : ZMod M) * ((χ h : (ZMod M)ˣ) : ZMod M) + 1 = 0 ∧
      (t = 2 → h = 1) ∧ (t = -2 → h = c)) :
    Nat.card (H ⧸ Subgroup.zpowers c) ≤ 3 ∧ IsCyclic (H ⧸ Subgroup.zpowers c) ∧
      (2 ∣ Nat.card (H ⧸ Subgroup.zpowers c) → ∃ lam : ZMod M, lam ^ 2 + 1 = 0) ∧
      (3 ∣ Nat.card (H ⧸ Subgroup.zpowers c) → ∃ lam : ZMod M, lam ^ 2 + lam + 1 = 0) := by
  classical
  have hc' : sc χ c = -1 := hc
  have htr' : ∀ h : H, ∃ t : ℤ, (t = -2 ∨ t = -1 ∨ t = 0 ∨ t = 1 ∨ t = 2) ∧
      (sc χ h) ^ 2 - (t : ZMod M) * (sc χ h) + 1 = 0 ∧ (t = 2 → h = 1) ∧ (t = -2 → h = c) := htr
  have hle := card_quot_le_three c χ hχ hc' hM htr'
  have hpos : 0 < Nat.card (H ⧸ Subgroup.zpowers c) := Nat.card_pos

  have lift : ∀ p : ℕ, p.Prime → p ∣ Nat.card (H ⧸ Subgroup.zpowers c) →
      ∃ h : H, h ≠ 1 ∧ h ≠ c ∧ (h ^ p = 1 ∨ h ^ p = c) := by
    intro p hp hdvd
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := H ⧸ Subgroup.zpowers c) p hdvd
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    have hq1 : (QuotientGroup.mk h : H ⧸ Subgroup.zpowers c) ≠ 1 := by
      intro e; rw [e, orderOf_one] at hq; exact hp.one_lt.ne' hq.symm
    have hnot : h ∉ Subgroup.zpowers c := fun hm => hq1 ((QuotientGroup.eq_one_iff h).mpr hm)
    have hp1 : (QuotientGroup.mk (h ^ p) : H ⧸ Subgroup.zpowers c) = 1 := by
      rw [QuotientGroup.mk_pow, ← hq, pow_orderOf_eq_one]
    have hmem : h ^ p ∈ Subgroup.zpowers c := (QuotientGroup.eq_one_iff _).mp hp1
    refine ⟨h, fun e => hnot (e ▸ Subgroup.one_mem _), fun e => hnot (e ▸ Subgroup.mem_zpowers c),
      mem_zpowers_c c χ hχ hc' hM hmem⟩
  refine ⟨hle, ?_, ?_, ?_⟩
  ·
    have : Nat.card (H ⧸ Subgroup.zpowers c) = 1 ∨ Nat.card (H ⧸ Subgroup.zpowers c) = 2 ∨
        Nat.card (H ⧸ Subgroup.zpowers c) = 3 := by omega
    rcases this with h1 | h2 | h3
    · haveI : Subsingleton (H ⧸ Subgroup.zpowers c) := (Nat.card_eq_one_iff_unique.mp h1).1
      exact isCyclic_of_subsingleton
    · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact isCyclic_of_prime_card h2
    · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact isCyclic_of_prime_card h3
  · intro h2
    obtain ⟨h, h1, hc0, hh⟩ := lift 2 Nat.prime_two h2
    rcases hh with e | e
    · rcases eq_one_or_eq_c_of_sq c χ hχ hc' hM htr' (by rw [← pow_two]; exact e) with e' | e'
      · exact absurd e' h1
      · exact absurd e' hc0
    · have h4 : h ^ 4 = 1 := by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, e, pow_two, c_sq c χ hχ hc']
      exact ⟨sc χ h, sq_eq_neg_one c χ hχ hc' htr' h4 h1 hc0⟩
  · intro h3
    obtain ⟨h, h1, hc0, hh⟩ := lift 3 Nat.prime_three h3
    have h6 : h ^ 6 = 1 := by
      rcases hh with e | e
      · rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, e, one_pow]
      · rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, e, pow_two, c_sq c χ hχ hc']
    rcases cube c χ hχ hc' hM htr' h h6 h1 hc0 with ⟨-, e⟩ | ⟨-, e⟩
    · exact ⟨sc χ h, e⟩
    · exact ⟨-sc χ h, by linear_combination e⟩

end S_Subgroup_card_quotient_zpowers_le_three_of_injective_of_sq_sub_mul_add_one_eq_zero
end P2MW
export P2MW.S_Subgroup_card_quotient_zpowers_le_three_of_injective_of_sq_sub_mul_add_one_eq_zero (solution)
