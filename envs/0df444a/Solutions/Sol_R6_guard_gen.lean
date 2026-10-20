-- Prove2me | solution 1 for R6.guard_gen
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T14:13:55.511497+00:00
-- url     : https://prove2.me/submissions/f09f675f-29ec-4fa7-be63-fa86a7560e74

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

theorem solution (E L T : ℝ) (s m : ℕ) (A : ℕ → ℝ) (hm : 2 ≤ m) (hs : 2 ≤ s) (hE : 0 ≤ E)
    (hL : 0 ≤ L) (hT : 0 < T)
    (hrec : ∀ e : ℕ, T ≤ e → ∃ cs : List ℕ, cs.length ≤ s ∧ (∀ c ∈ cs, m * c ≤ (m - 1) * e) ∧
      A e ≤ E + (cs.map A).sum)
    (hleaf : ∀ e : ℕ, (e : ℝ) < T → A e ≤ L) :
    ∀ e : ℕ, A e ≤ (E + L) * (2 * (s : ℝ) ^ (max 0 (m * (Real.log e - Real.log T) + 1)) - 1) := by
  have hs1 : (1:ℝ) ≤ s := by exact_mod_cast (by omega : 1 ≤ s)
  have hs2 : (2:ℝ) ≤ s := by exact_mod_cast hs
  have hEL : 0 ≤ E + L := by linarith
  set B : ℝ → ℝ := fun x => (E + L) * (2 * (s:ℝ) ^ x - 1) with hB
  have hBmono : ∀ x y : ℝ, x ≤ y → B x ≤ B y := by
    intro x y hxy
    simp only [hB]
    have := Real.rpow_le_rpow_of_exponent_le hs1 hxy
    nlinarith
  have hBL : ∀ x : ℝ, 0 ≤ x → L ≤ B x := by
    intro x hx
    simp only [hB]
    have := Real.one_le_rpow hs1 hx
    nlinarith
  have hB0 : ∀ x : ℝ, 0 ≤ x → 0 ≤ B x := fun x hx => le_trans hL (hBL x hx)
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
  change A e ≤ B (max 0 ((m:ℝ) * (Real.log e - Real.log T) + 1))
  by_cases he : (e:ℝ) < T
  · exact le_trans (hleaf e he) (hBL _ (le_max_left _ _))
  push_neg at he
  have hepos : (0:ℝ) < e := lt_of_lt_of_le hT he
  have hlogle : Real.log T ≤ Real.log e := Real.log_le_log hT he
  have hmpos : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  set xe := (m:ℝ) * (Real.log e - Real.log T) + 1 with hxe
  have hxe1 : 1 ≤ xe := by
    have : 0 ≤ (m:ℝ) * (Real.log e - Real.log T) := mul_nonneg hmpos.le (by linarith)
    linarith
  rw [max_eq_right (by linarith)]
  obtain ⟨cs, hlen, hcs, hA⟩ := hrec e he
  have hc : ∀ c ∈ cs, A c ≤ B (xe - 1) := by
    intro c hcmem
    have hmc := hcs c hcmem
    by_cases hcT : (c:ℝ) < T
    · exact le_trans (hleaf c hcT) (hBL _ (by linarith))
    push_neg at hcT
    have hcpos : (0:ℝ) < c := lt_of_lt_of_le hT hcT
    have hce : c < e := by
      have he0 : 0 < e := by exact_mod_cast hepos
      have : m * c < m * e := by
        calc m * c ≤ (m-1) * e := hmc
          _ < m * e := Nat.mul_lt_mul_of_pos_right (by omega) he0
      exact Nat.lt_of_mul_lt_mul_left this
    have h1 := ih c hce
    have hmcR : (m:ℝ) * c ≤ ((m:ℝ) - 1) * e := by
      have : ((m - 1 : ℕ) : ℝ) = (m:ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      rw [← this]; exact_mod_cast hmc
    have hlog : 1 ≤ (m:ℝ) * (Real.log e - Real.log c) := by
      have hq : 1 - ((e:ℝ)/c)⁻¹ ≤ Real.log ((e:ℝ)/c) :=
        Real.one_sub_inv_le_log_of_pos (div_pos hepos hcpos)
      rw [inv_div, Real.log_div hepos.ne' hcpos.ne'] at hq
      have hce' : (c:ℝ) / e ≤ ((m:ℝ) - 1) / m := by
        rw [div_le_div_iff₀ hepos hmpos]; linarith
      have : (1:ℝ) ≤ m * (1 - c/e) := by
        have h2 : ((m:ℝ) - 1) / m = 1 - 1/m := by field_simp
        rw [h2] at hce'
        have : (1:ℝ)/m ≤ 1 - c/e := by linarith
        calc (1:ℝ) = m * (1/m) := by field_simp
          _ ≤ m * (1 - c/e) := mul_le_mul_of_nonneg_left this hmpos.le
      nlinarith
    have hlogc : Real.log T ≤ Real.log c := Real.log_le_log hT hcT
    have hxc0 : 0 ≤ (m:ℝ) * (Real.log c - Real.log T) + 1 := by
      have : 0 ≤ (m:ℝ) * (Real.log c - Real.log T) := mul_nonneg hmpos.le (by linarith)
      linarith
    have hxc : (m:ℝ) * (Real.log c - Real.log T) + 1 ≤ xe - 1 := by
      rw [hxe]; nlinarith
    change A c ≤ B (max 0 ((m:ℝ) * (Real.log c - Real.log T) + 1)) at h1
    rw [max_eq_right hxc0] at h1
    exact le_trans h1 (hBmono _ _ hxc)
  have hsum : (cs.map A).sum ≤ s * B (xe - 1) := by
    have := List.sum_le_card_nsmul (cs.map A) (B (xe - 1)) (by
      intro x hx; obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hx; exact hc c hc')
    rw [List.length_map, nsmul_eq_mul] at this
    calc _ ≤ _ := this
      _ ≤ (s:ℝ) * B (xe - 1) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) (hB0 _ (by linarith))
  have key : E + s * B (xe - 1) ≤ B xe := by
    have hp : (s:ℝ) ^ xe = (s:ℝ) ^ (xe - 1) * s := by
      rw [← Real.rpow_add_one (by positivity)]; ring_nf
    have hP1 : 1 ≤ (s:ℝ) ^ (xe - 1) := Real.one_le_rpow hs1 (by linarith)
    simp only [hB, hp]
    nlinarith [mul_nonneg hEL (sub_nonneg.mpr hP1)]
  linarith
