-- Prove2me | solution 1 for PerimeterPatrol.Visible.patrolValue_monotone
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T22:44:05.7408+00:00
-- url     : https://prove2.me/submissions/3fe503f4-5048-4eba-8359-50dc05a0a051

import Mathlib
import Definitions.Def_PerimeterPatrol_Visible_Model

namespace PerimeterPatrol.Visible

/-- tangent line of `n ↦ 1 - q^n` on `[n, n+1]` -/
noncomputable def PPL (q : ℝ) (n : ℕ) (c : ℝ) : ℝ := 1 - q ^ n + (c - n) * (q ^ n - q ^ (n + 1))

lemma PP_valueC_eq (p c : ℝ) (hc : 0 ≤ c) : valueC c p = PPL (1 - p) ⌊c⌋₊ c := by
  unfold valueC PPL
  have h1 := Nat.floor_le hc
  have h2 := Nat.le_ceil c
  rcases Nat.eq_or_lt_of_le (Nat.ceil_le_floor_add_one c) with h | h
  · rw [h]; push_cast; ring
  · have hle : ⌈c⌉₊ ≤ ⌊c⌋₊ := Nat.lt_add_one_iff.mp h
    have hge : ⌊c⌋₊ ≤ ⌈c⌉₊ := Nat.floor_le_ceil c
    have he : ⌈c⌉₊ = ⌊c⌋₊ := le_antisymm hle hge
    have : (⌊c⌋₊ : ℝ) = c := by
      apply le_antisymm h1; rw [← he]; exact h2
    rw [he, this]; ring

lemma PP_valueC_mono_c (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    MonotoneOn (fun c => valueC c p) (Set.Ici 0) := by
  intro c hc c' hc' hcc
  simp only [Set.mem_Ici] at hc hc'
  simp only
  rw [PP_valueC_eq p c hc, PP_valueC_eq p c' hc']
  set q := 1 - p with hq
  have hq0 : 0 ≤ q := by rw [hq]; linarith
  have hq1 : q ≤ 1 := by rw [hq]; linarith
  have hfl : ⌊c⌋₊ ≤ ⌊c'⌋₊ := Nat.floor_le_floor hcc
  have slope : ∀ n : ℕ, 0 ≤ q ^ n - q ^ (n + 1) := by
    intro n
    have : q ^ (n + 1) ≤ q ^ n := pow_le_pow_of_le_one hq0 hq1 (Nat.le_succ n)
    linarith
  rcases Nat.eq_or_lt_of_le hfl with h | h
  · rw [← h]; unfold PPL
    nlinarith [slope ⌊c⌋₊]
  · unfold PPL
    have a1 : c < (⌊c⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one c
    have a2 : (⌊c'⌋₊ : ℝ) ≤ c' := Nat.floor_le hc'
    have a3 : q ^ ⌊c'⌋₊ ≤ q ^ (⌊c⌋₊ + 1) := pow_le_pow_of_le_one hq0 hq1 h
    have a4 := slope ⌊c⌋₊
    have a5 := slope ⌊c'⌋₊
    nlinarith

lemma PP_valueC_mono_p (c : ℝ) (hc : 0 ≤ c) :
    MonotoneOn (fun q => valueC c q) (Set.Ioc 0 1) := by
  intro p hp p' hp' hpp
  simp only [Set.mem_Ioc] at hp hp'
  unfold valueC
  have ha : 0 ≤ c - ⌊c⌋₊ := by linarith [Nat.floor_le hc]
  have hb : 0 ≤ 1 - c + ⌊c⌋₊ := by linarith [Nat.lt_floor_add_one c]
  have e1 : (1 - p') ^ ⌈c⌉₊ ≤ (1 - p) ^ ⌈c⌉₊ := pow_le_pow_left₀ (by linarith) (by linarith) _
  have e2 : (1 - p') ^ ⌊c⌋₊ ≤ (1 - p) ^ ⌊c⌋₊ := pow_le_pow_left₀ (by linarith) (by linarith) _
  nlinarith [mul_le_mul_of_nonneg_left e1 ha, mul_le_mul_of_nonneg_left e2 hb]

end PerimeterPatrol.Visible

open PerimeterPatrol.Visible in
theorem solution (lam t p : ℝ) (hlam : 0 < lam) (ht : 0 < t) (hp0 : 0 < p) (hp1 : p ≤ 1) : MonotoneOn (fun l : ℝ => patrolValue l t p) (Set.Ioi 0) ∧ MonotoneOn (fun u : ℝ => patrolValue lam u p) (Set.Ioi 0) ∧ MonotoneOn (fun q : ℝ => patrolValue lam t q) (Set.Ioc 0 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro l hl l' hl' hll
    simp only [Set.mem_Ioi] at hl hl'
    unfold patrolValue
    exact PP_valueC_mono_c p hp0.le hp1 (Set.mem_Ici.mpr (by positivity))
      (Set.mem_Ici.mpr (by positivity)) (mul_le_mul_of_nonneg_right hll ht.le)
  · intro u hu u' hu' huu
    simp only [Set.mem_Ioi] at hu hu'
    unfold patrolValue
    exact PP_valueC_mono_c p hp0.le hp1 (Set.mem_Ici.mpr (by positivity))
      (Set.mem_Ici.mpr (by positivity)) (mul_le_mul_of_nonneg_left huu hlam.le)
  · intro q hq q' hq' hqq
    unfold patrolValue
    exact PP_valueC_mono_p (lam * t) (by positivity) hq hq' hqq
