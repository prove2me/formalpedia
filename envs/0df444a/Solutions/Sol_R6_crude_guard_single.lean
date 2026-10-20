-- Prove2me | solution 1 for R6.crude_guard_single
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T14:17:41.032294+00:00
-- url     : https://prove2.me/submissions/db20e2da-12ec-4c85-b942-77a51e759167

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

theorem r6_gg (E L T : ℝ) (s m : ℕ) (A : ℕ → ℝ) (hm : 2 ≤ m) (hs : 2 ≤ s) (hE : 0 ≤ E)
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

theorem r6_cg (E : ℝ) (s m : ℕ) (d β : ℝ) (A : ℕ → ℝ) (hm : 2 ≤ m) (hs : 2 ≤ s)
    (hβ : 0 ≤ β ∧ β ≤ 1) (hd : 1 ≤ d) (hE : 0 ≤ E)
    (hrec : ∀ e : ℕ, d ^ β ≤ e → ∃ cs : List ℕ, cs.length ≤ s ∧
      (∀ c ∈ cs, m * c ≤ (m - 1) * e) ∧ A e ≤ E + (cs.map A).sum)
    (hleaf : ∀ e : ℕ, (e : ℝ) < d ^ β → A e ≤ 8 * d ^ β) :
    ∀ e : ℕ, (e : ℝ) ≤ d → A e ≤ 2 * (E + 8 * d ^ β) * (s : ℝ) ^ (1 + m * (1 - β) * Real.log d) := by
  have hd0 : (0:ℝ) < d := by linarith
  have hT : (0:ℝ) < d ^ β := Real.rpow_pos_of_pos hd0 β
  have hL : (0:ℝ) ≤ 8 * d ^ β := by positivity
  have hs1 : (1:ℝ) ≤ s := by exact_mod_cast (by omega : 1 ≤ s)
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg hd
  have hmpos : (0:ℝ) ≤ m := by positivity
  intro e he
  have h := r6_gg E (8 * d ^ β) (d ^ β) s m A hm hs hE hL hT hrec hleaf e
  rw [Real.log_rpow hd0] at h
  have hloge : Real.log e ≤ Real.log d := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · subst h0; simpa using hlogd
    · exact Real.log_le_log (by exact_mod_cast h0) he
  have hx : max 0 ((m:ℝ) * (Real.log e - β * Real.log d) + 1) ≤ 1 + m * (1 - β) * Real.log d := by
    apply max_le
    · have : 0 ≤ (m:ℝ) * (1 - β) * Real.log d := mul_nonneg (mul_nonneg hmpos (by linarith)) hlogd
      linarith
    · have : (m:ℝ) * (Real.log e - β * Real.log d) ≤ m * ((1 - β) * Real.log d) :=
        mul_le_mul_of_nonneg_left (by linarith) hmpos
      linarith
  have hp := Real.rpow_le_rpow_of_exponent_le hs1 hx
  have hpos : 0 ≤ (s:ℝ) ^ (max 0 ((m:ℝ) * (Real.log e - β * Real.log d) + 1)) := by positivity
  have hEL : 0 ≤ E + 8 * d ^ β := by linarith
  calc A e ≤ _ := h
    _ ≤ (E + 8 * d ^ β) * (2 * (s:ℝ) ^ (1 + m * (1 - β) * Real.log d)) := by
        apply mul_le_mul_of_nonneg_left _ hEL; linarith
    _ = _ := by ring

theorem r6_cgpow (E : ℝ) (s m : ℕ) (d β : ℝ) (A : ℕ → ℝ) (hm : 2 ≤ m) (hs : 2 ≤ s)
    (hβ : 0 ≤ β ∧ β ≤ 1) (hd : 1 ≤ d) (hE : 0 ≤ E)
    (hrec : ∀ e : ℕ, d ^ β ≤ e → ∃ cs : List ℕ, cs.length ≤ s ∧
      (∀ c ∈ cs, m * c ≤ (m - 1) * e) ∧ A e ≤ E + (cs.map A).sum)
    (hleaf : ∀ e : ℕ, (e : ℝ) < d ^ β → A e ≤ 8 * d ^ β) :
    ∀ e : ℕ, (e : ℝ) ≤ d →
      A e ≤ 2 * s * (E + 8) * d ^ (β + m * (1 - β) * Real.log s) := by
  intro e he
  have h := r6_cg E s m d β A hm hs hβ hd hE hrec hleaf e he
  have hd0 : (0:ℝ) < d := by linarith
  have hs0 : (0:ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have hdb : 1 ≤ d ^ β := Real.one_le_rpow hd hβ.1
  have h1 : (s:ℝ) ^ (1 + m * (1 - β) * Real.log d) = s * d ^ (m * (1 - β) * Real.log s) := by
    rw [Real.rpow_add hs0, Real.rpow_one]
    congr 1
    rw [Real.rpow_def_of_pos hs0, Real.rpow_def_of_pos hd0]; congr 1; ring
  have h2 : (d:ℝ) ^ (β + m * (1 - β) * Real.log s) = d ^ β * d ^ (m * (1 - β) * Real.log s) :=
    Real.rpow_add hd0 _ _
  rw [h1] at h; rw [h2]
  have hq : 0 ≤ (d:ℝ) ^ (m * (1 - β) * Real.log s) := by positivity
  have h3 : E + 8 * d ^ β ≤ (E + 8) * d ^ β := by nlinarith
  calc A e ≤ _ := h
    _ = 2 * s * d ^ (m * (1 - β) * Real.log s) * (E + 8 * d ^ β) := by ring
    _ ≤ 2 * s * d ^ (m * (1 - β) * Real.log s) * ((E + 8) * d ^ β) := by
        apply mul_le_mul_of_nonneg_left h3; positivity
    _ = _ := by ring

theorem r6_cgC1 (E : ℝ) (s m : ℕ) (d β C1 : ℝ) (A : ℕ → ℝ) (hm : 2 ≤ m) (hs : 2 ≤ s)
    (hβ : 0 ≤ β ∧ β ≤ 1) (hd : 1 ≤ d) (hE : 0 ≤ E) (hC1 : 2 + m * Real.log s ≤ C1)
    (hrec : ∀ e : ℕ, d ^ β ≤ e → ∃ cs : List ℕ, cs.length ≤ s ∧
      (∀ c ∈ cs, m * c ≤ (m - 1) * e) ∧ A e ≤ E + (cs.map A).sum)
    (hleaf : ∀ e : ℕ, (e : ℝ) < d ^ β → A e ≤ 8 * d ^ β) :
    ∀ e : ℕ, (e : ℝ) ≤ d → A e ≤ 2 * s * (E + 8) * d ^ C1 := by
  intro e he
  have h := r6_cgpow E s m d β A hm hs hβ hd hE hrec hleaf e he
  have hlogs : 0 ≤ Real.log s := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ s))
  have hmpos : (0:ℝ) ≤ m := by positivity
  have hx : β + m * (1 - β) * Real.log s ≤ C1 := by
    have : (m:ℝ) * (1 - β) * Real.log s ≤ m * Real.log s := by
      have := mul_nonneg hmpos hlogs
      nlinarith [hβ.1]
    linarith [hβ.2]
  have := Real.rpow_le_rpow_of_exponent_le hd hx
  calc A e ≤ _ := h
    _ ≤ _ := by apply mul_le_mul_of_nonneg_left this; positivity

theorem solution (E : ℝ) (s m : ℕ) (d β : ℝ) (A : ℕ → ℝ) (hm : 2 ≤ m) (hs : 2 ≤ s)
    (hβ : 0 ≤ β ∧ β ≤ 1) (hd : 1 ≤ d) (hE : 0 ≤ E)
    (hrec : ∀ e : ℕ, d ^ β ≤ e → A e ≤ E + s * A ((m - 1) * e / m))
    (hleaf : ∀ e : ℕ, (e : ℝ) < d ^ β → A e ≤ 8 * d ^ β) :
    ∀ e : ℕ, (e : ℝ) ≤ d → A e ≤ 2 * (E + 8 * d ^ β) * (s : ℝ) ^ (1 + m * (1 - β) * Real.log d) := by
  refine r6_cg E s m d β A hm hs hβ hd hE ?_ hleaf
  intro e he
  refine ⟨List.replicate s ((m - 1) * e / m), by simp, ?_, ?_⟩
  · intro c hc
    rw [List.eq_of_mem_replicate hc, mul_comm]
    exact Nat.div_mul_le_self _ _
  · simpa [List.sum_replicate, nsmul_eq_mul] using hrec e he
