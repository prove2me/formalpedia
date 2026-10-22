-- Prove2me | solution 1 for SourceTheory.EqualSources.linear_on_half
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:04:48.460835+00:00
-- url     : https://prove2.me/submissions/ff76a351-4337-467b-a5bf-2d05f4c6eca9

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

set_option autoImplicit false
open Set

theorem solution (φ ψ : ℝ → ℝ) (hφ : SourceTheory.Uniform.IsTransformation φ)
    (hψ : ∀ p ∈ Icc (0 : ℝ) 1, ψ (φ p) = p ∧ φ (ψ p) = p) (hhalf : φ (1 / 2) = 1 / 2)
    (hsub : ∀ p ε : ℝ, 0 ≤ p → 0 ≤ ε → p + ε ≤ 1 / 2 → φ (p + ε) - φ p ≤ φ ε)
    (hsubψ : ∀ p ε : ℝ, 0 ≤ p → 0 ≤ ε → p + ε ≤ 1 / 2 → ψ (p + ε) - ψ p ≤ ψ ε) :
    ∃ c : ℝ, ∀ p ∈ Icc (0 : ℝ) (1 / 2), φ p = c * p := by
  obtain ⟨⟨hmaps, hmono, h0, h1⟩, hcont⟩ := hφ
  -- monotonicity of φ on [0,1]
  have hmon : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → φ a ≤ φ b := by
    intro a b ha hab hb
    exact hmono.monotoneOn ⟨ha, hab.trans hb⟩ ⟨ha.trans hab, hb⟩ hab
  have hφ0 : ∀ a, 0 ≤ a → a ≤ 1 → 0 ≤ φ a ∧ φ a ≤ 1 := by
    intro a ha ha1
    have := hmaps (show a ∈ Icc (0:ℝ) 1 from ⟨ha, ha1⟩)
    exact this
  -- ψ maps [0,1] into [0,1]
  have hψmem : ∀ q : ℝ, 0 ≤ q → q ≤ 1 → 0 ≤ ψ q ∧ ψ q ≤ 1 := by
    intro q hq0 hq1
    have : q ∈ φ '' Icc (0:ℝ) 1 := by
      have := intermediate_value_Icc (show (0:ℝ) ≤ 1 by norm_num) hcont
      rw [h0, h1] at this
      exact this ⟨hq0, hq1⟩
    obtain ⟨p, hp, hpq⟩ := this
    have := (hψ p hp).1
    rw [hpq] at this
    rw [this]; exact hp
  -- key: φ x + φ (1/2 - x) ≤ 1/2
  have hsym : ∀ x : ℝ, 0 ≤ x → x ≤ 1 / 2 → φ x + φ (1 / 2 - x) ≤ 1 / 2 := by
    intro x hx hx2
    have hu := hφ0 x hx (by linarith)
    have hux : φ x ≤ 1 / 2 := by
      rw [← hhalf]; exact hmon x (1/2) hx hx2 (by norm_num)
    have hv : 0 ≤ 1 / 2 - φ x := by linarith
    have := hsubψ (φ x) (1 / 2 - φ x) hu.1 hv (by linarith)
    have e1 : ψ (φ x + (1 / 2 - φ x)) = ψ (1/2) := by ring_nf
    rw [e1] at this
    have e2 : ψ (1/2) = 1/2 := by
      have := (hψ (1/2) ⟨by norm_num, by norm_num⟩).1
      -- ψ (φ (1/2)) = 1/2
      rw [hhalf] at this; exact this
    rw [e2, (hψ x ⟨hx, by linarith⟩).1] at this
    have hm := hψmem (1 / 2 - φ x) hv (by linarith)
    have hψv := (hψ (1 / 2 - φ x) ⟨hv, by linarith⟩).2
    have : φ (1/2 - x) ≤ φ (ψ (1 / 2 - φ x)) :=
      hmon _ _ (by linarith) (by linarith) hm.2
    linarith
  -- additivity
  have hadd : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x + y ≤ 1 / 2 → φ (x + y) = φ x + φ y := by
    intro x y hx hy hxy
    apply le_antisymm
    · have := hsub x y hx hy hxy; linarith
    · have hx2 : x ≤ 1/2 := by linarith
      have hs := hsym x hx hx2
      have hy' : φ y ≤ φ (1/2 - x) := hmon _ _ hy (by linarith) (by linarith)
      have hux := hφ0 x hx (by linarith)
      have huy := hφ0 y hy (by linarith)
      have hsum : φ x + φ y ≤ 1 / 2 := by linarith
      have := hsubψ (φ x) (φ y) hux.1 huy.1 hsum
      rw [(hψ x ⟨hx, by linarith⟩).1, (hψ y ⟨hy, by linarith⟩).1] at this
      have hm := hψmem (φ x + φ y) (by linarith [hux.1, huy.1]) (by linarith)
      have h2 := (hψ (φ x + φ y) ⟨by linarith [hux.1, huy.1], by linarith⟩).2
      have : φ (ψ (φ x + φ y)) ≤ φ (x + y) :=
        hmon _ _ hm.1 (by linarith) (by linarith)
      linarith
  refine ⟨1, fun p hp => ?_⟩
  obtain ⟨hp0, hp2⟩ := hp
  rw [one_mul]
  -- values on the grid k/(2N)
  have hgrid : ∀ N : ℕ, 1 ≤ N → ∀ k : ℕ, k ≤ N → φ (k * (1 / (2 * N))) = k / (2 * N) := by
    intro N hN
    have hNpos : (0:ℝ) < N := by exact_mod_cast hN
    set t : ℝ := 1 / (2 * N) with ht
    have htpos : 0 < t := by positivity
    have hlin : ∀ k : ℕ, k ≤ N → φ (k * t) = k * φ t := by
      intro k
      induction k with
      | zero => intro _; simp [h0]
      | succ k ih =>
        intro hk
        have hk' : k ≤ N := by omega
        have e : ((k+1 : ℕ) : ℝ) * t = k * t + t := by push_cast; ring
        rw [e, hadd (k * t) t (by positivity) htpos.le, ih hk']
        · push_cast; ring
        · have : ((k + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hk
          have h2 : ((k + 1 : ℕ):ℝ) * t ≤ N * t := mul_le_mul_of_nonneg_right this htpos.le
          have h3 : (N:ℝ) * t = 1 / 2 := by rw [ht]; field_simp
          rw [e] at h2; linarith
    have htN : φ t = t := by
      have := hlin N le_rfl
      have h3 : (N:ℝ) * t = 1 / 2 := by rw [ht]; field_simp
      rw [h3, hhalf] at this
      have : (N:ℝ) * φ t = N * t := by rw [← this, h3]
      exact mul_left_cancel₀ hNpos.ne' this
    intro k hk
    rw [hlin k hk, htN, ht]
    field_simp
  -- sandwich
  have hclose : ∀ N : ℕ, 1 ≤ N → |φ p - p| ≤ 1 / (2 * N) := by
    intro N hN
    have hNpos : (0:ℝ) < N := by exact_mod_cast hN
    have h2N : (0:ℝ) < 2 * N := by positivity
    set k : ℕ := ⌊2 * N * p⌋₊ with hk
    have hk1 : (k : ℝ) ≤ 2 * N * p := Nat.floor_le (by positivity)
    have hk2 : 2 * N * p < k + 1 := Nat.lt_floor_add_one _
    have hkN : k ≤ N := by
      have : (k : ℝ) ≤ N := by nlinarith
      exact_mod_cast this
    have hgk := hgrid N hN k hkN
    have hkp : (k:ℝ) * (1 / (2 * N)) ≤ p := by
      rw [mul_one_div, div_le_iff₀ h2N]; linarith
    have hlow : (k:ℝ) / (2 * N) ≤ φ p := by
      rw [← hgk]
      exact hmon _ _ (by positivity) hkp (by linarith)
    have hlow' : p - 1 / (2 * N) ≤ φ p := by
      have : p - 1 / (2 * N) ≤ k / (2 * N) := by
        have e : p - 1 / (2 * (N:ℝ)) = (2 * N * p - 1) / (2 * N) := by field_simp
        rw [e]
        exact div_le_div_of_nonneg_right (by linarith) h2N.le
      linarith
    have hup : φ p ≤ p + 1 / (2 * N) := by
      rcases Nat.lt_or_ge k N with hlt | hge
      · have hg1 := hgrid N hN (k + 1) hlt
        have hpk : p ≤ ((k + 1 : ℕ) : ℝ) * (1 / (2 * N)) := by
          rw [mul_one_div, le_div_iff₀ h2N]; push_cast; linarith
        have : φ p ≤ φ (((k + 1 : ℕ) : ℝ) * (1 / (2 * N))) := by
          refine hmon _ _ hp0 hpk ?_
          have : ((k + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hlt
          calc ((k + 1 : ℕ) : ℝ) * (1 / (2 * N)) ≤ N * (1 / (2 * N)) :=
                mul_le_mul_of_nonneg_right this (by positivity)
            _ = 1 / 2 := by field_simp
            _ ≤ 1 := by norm_num
        rw [hg1] at this
        have e : ((k + 1 : ℕ) : ℝ) / (2 * N) ≤ p + 1 / (2 * N) := by
          rw [div_le_iff₀ h2N]
          have : (p + 1 / (2 * N)) * (2 * N) = 2 * N * p + 1 := by field_simp
          rw [this]; push_cast; linarith
        linarith
      · have hkeq : k = N := le_antisymm hkN hge
        have hp12 : p = 1 / 2 := by
          have hkc : (k : ℝ) = N := by exact_mod_cast hkeq
          have : (N : ℝ) ≤ 2 * N * p := by linarith [hk1, hkc]
          have : (1:ℝ) / 2 ≤ p := by nlinarith
          linarith
        rw [hp12, hhalf]
        have : (0:ℝ) ≤ 1 / (2 * N) := by positivity
        linarith
    rw [abs_le]; constructor <;> linarith
  by_contra hne
  have hpos : 0 < |φ p - p| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / |φ p - p|)
  have hN1 : 1 ≤ N := by
    have : (0:ℝ) < N := lt_trans (by positivity) hN
    exact_mod_cast this
  have := hclose N hN1
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN1
  have h3 : 1 / |φ p - p| < N := hN
  rw [div_lt_iff₀ hpos] at h3
  have h4 : 1 / (2 * (N:ℝ)) < |φ p - p| := by
    rw [div_lt_iff₀ (by positivity)]; nlinarith
  linarith
