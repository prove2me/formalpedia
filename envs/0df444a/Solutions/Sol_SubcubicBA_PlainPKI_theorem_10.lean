-- Prove2me | solution 1 for SubcubicBA.PlainPKI.theorem_10
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-23T23:43:24.163808+00:00
-- url     : https://prove2.me/submissions/2d880075-b080-476d-872d-799611195e61

import Mathlib
import Definitions.Def_SubcubicBA_PlainPKI_Recurrences

open SubcubicBA.PlainPKI

set_option maxHeartbeats 1600000 in
theorem solution (C₀ : ℝ) (hC₀ : 0 < C₀) :
    ∃ B₀ c₀ : ℝ, 0 < B₀ ∧ 0 < c₀ ∧ ∀ B c : ℝ, B₀ ≤ B → c₀ ≤ c → ∃ A : ℝ, 0 < A ∧
      ∀ (κ : ℕ) (R : ℕ → ℝ), 1 ≤ κ → RoundRecurrence C₀ B c κ R →
        ∀ n : ℕ, 1 ≤ n → R n ≤ A * n := by
  have hs1 : (36 / 10 : ℝ) < Real.sqrt 13 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hs2 : Real.sqrt 13 < 361 / 100 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hp1 : (13 / 10 : ℝ) < pExp := by unfold pExp; linarith
  have hp2 : pExp < 261 / 200 := by unfold pExp; linarith
  have hθ2 : (2:ℝ) ^ ((19:ℝ) / 20) < 2 := by
    have := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2) (by norm_num : (19:ℝ) / 20 < 1)
    simpa using this
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g = 2 - (2:ℝ) ^ ((19:ℝ) / 20) := ⟨_, rfl⟩
  have hg0 : 0 < g := by rw [hg]; linarith
  refine ⟨1, max 2 (32 * C₀ / g), one_pos, by positivity, fun B c hB hc => ?_⟩
  have hc2 : 2 ≤ c := le_trans (le_max_left _ _) hc
  have hcg : 32 * C₀ ≤ c * g := by
    have := le_trans (le_max_right _ _) hc
    rwa [div_le_iff₀ hg0] at this
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : ℝ, A₀ = max 2 (8 * C₀ * (c + 2) / g) := ⟨_, rfl⟩
  have hA2 : 2 ≤ A₀ := hA₀ ▸ le_max_left _ _
  have hA0 : 0 < A₀ := by linarith
  have hAg : 8 * C₀ * (c + 2) ≤ A₀ * g := by
    have : 8 * C₀ * (c + 2) / g ≤ A₀ := hA₀ ▸ le_max_right _ _
    rwa [div_le_iff₀ hg0] at this
  have hclog : ∀ m : ℕ, 1 ≤ m → (2:ℝ) ^ (Nat.clog 2 m) ≤ 2 * m := by
    intro m hm
    have : 2 ^ (Nat.clog 2 m) ≤ 2 * m := by
      rcases Nat.eq_or_lt_of_le hm with h | h
      · subst h; simp [Nat.clog_one_right]
      · have h1 := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) h
        have h2 : 0 < Nat.clog 2 m := Nat.clog_pos (by norm_num) h
        calc 2 ^ Nat.clog 2 m = 2 * 2 ^ (Nat.clog 2 m).pred := by
              rw [← pow_succ']; exact congrArg (2 ^ ·) (Nat.succ_pred_eq_of_pos h2).symm
          _ ≤ 2 * m := Nat.mul_le_mul_left 2 h1.le
    exact_mod_cast this
  refine ⟨2 * A₀, by positivity, fun κ R hκ hR => ?_⟩
  obtain ⟨hR0, hR1, hrec⟩ := hR
  have hθk : ∀ k : ℕ, (2:ℝ) ^ ((19:ℝ) / 20 * k) ≤ 2 ^ k := fun k => by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by have := k.cast_nonneg (α := ℝ); nlinarith)
  let Ψ : ℕ → ℝ := fun k => A₀ * 2 ^ k - A₀ / 2 * (2:ℝ) ^ ((19:ℝ) / 20 * k)
  have hΨle : ∀ k, Ψ k ≤ A₀ * 2 ^ k := fun k => by
    have : 0 ≤ A₀ / 2 * (2:ℝ) ^ ((19:ℝ) / 20 * k) := mul_nonneg (by linarith) (by positivity)
    simp only [Ψ]; linarith
  have hΨ1 : ∀ k, 1 ≤ Ψ k := fun k => by
    have h1 : (1:ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have h2 := mul_le_mul_of_nonneg_left (hθk k) (by linarith : (0:ℝ) ≤ A₀ / 2)
    have h3 := mul_le_mul_of_nonneg_right hA2 (by positivity : (0:ℝ) ≤ 2 ^ k)
    simp only [Ψ]; linarith
  have hstep : ∀ k : ℕ, Ψ (k + 1) = 2 * Ψ k + A₀ / 2 * g * (2:ℝ) ^ ((19:ℝ) / 20 * k) := fun k => by
    simp only [Ψ]
    rw [hg, show (19:ℝ) / 20 * ((k + 1 : ℕ) : ℝ) = 19 / 20 * k + 19 / 20 by push_cast; ring,
      Real.rpow_add (by norm_num : (0:ℝ) < 2), pow_succ]
    ring
  have key : ∀ k : ℕ, ∀ m : ℕ, 1 ≤ m → m ≤ 2 ^ k → R m ≤ Ψ k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k IH =>
    intro m hm1 hmk
    rcases Nat.eq_or_lt_of_le hm1 with h | hm2
    · subst h; exact le_trans hR1 (hΨ1 k)
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := by
      rcases k with _ | k'
      · simp at hmk; omega
      · exact ⟨k', rfl⟩
    have hlin : ∀ m' : ℕ, 1 ≤ m' → m' ≤ 2 ^ k' → R m' ≤ 2 * A₀ * m' := by
      intro m' h1 h2
      have hj : Nat.clog 2 m' ≤ k' := Nat.clog_le_of_le_pow h2
      have h3 := IH _ (by omega) m' h1 (Nat.le_pow_clog (by norm_num) m')
      have h4 := hΨle (Nat.clog 2 m')
      have h5 := mul_le_mul_of_nonneg_left (hclog m' h1) hA0.le
      linarith
    have hrm := hrec m (by omega)
    dsimp only at hrm
    have hmpos : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hm1R : (1:ℝ) ≤ m := by exact_mod_cast hm1
    have hNk : (m:ℝ) ≤ 2 ^ k' * 2 := by
      have : (m:ℝ) ≤ 2 ^ (k' + 1) := by exact_mod_cast hmk
      rwa [pow_succ] at this
    have hQ1 : (1:ℝ) ≤ (2:ℝ) ^ ((19:ℝ) / 20 * k') := Real.one_le_rpow (by norm_num) (by positivity)
    have hNθ : (m:ℝ) ^ ((19:ℝ) / 20) ≤ 2 * (2:ℝ) ^ ((19:ℝ) / 20 * k') := by
      have h1 : (m:ℝ) ^ ((19:ℝ) / 20) ≤ ((2:ℝ) ^ (k' + 1)) ^ ((19:ℝ) / 20) :=
        Real.rpow_le_rpow hmpos.le (by rw [pow_succ]; exact hNk) (by norm_num)
      have h2 : ((2:ℝ) ^ (k' + 1)) ^ ((19:ℝ) / 20) =
          (2:ℝ) ^ ((19:ℝ) / 20) * (2:ℝ) ^ ((19:ℝ) / 20 * k') := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
        congr 1; push_cast; ring
      have h3 := mul_le_mul_of_nonneg_right hθ2.le (by positivity : (0:ℝ) ≤ (2:ℝ) ^ ((19:ℝ) / 20 * k'))
      linarith
    have hhalf : R ⌈(m:ℝ) / 2⌉₊ ≤ Ψ k' := by
      apply IH k' (by omega)
      · exact Nat.one_le_ceil_iff.2 (by positivity)
      · rw [Nat.ceil_le]; push_cast; linarith
    rw [hstep k']
    have hAgQ := mul_le_mul_of_nonneg_left hQ1 (mul_nonneg hA0.le hg0.le)
    by_cases hsm : (m:ℝ) ≤ B * (κ:ℝ) ^ 4
    · have hM : (paramM B c κ m : ℝ) = m := by rw [paramM, if_pos hsm]
      have hB' : (paramB B c κ m : ℝ) = 1 := by rw [paramB, if_pos hsm, Nat.cast_one]
      rw [hM, hB', div_self hmpos.ne', Real.one_rpow, Nat.ceil_one] at hrm
      have h1 := mul_le_mul_of_nonneg_left hR1 hC₀.le
      have h2 := mul_le_mul_of_nonneg_left hc2 hC₀.le
      nlinarith
    · have hM : (paramM B c κ m : ℝ) = (⌈c * ((κ:ℝ) * m) ^ (pExp - 1)⌉₊ : ℕ) := by
        rw [paramM, if_neg hsm]
      have hB' : (paramB B c κ m : ℝ) = (⌈c * ((κ:ℝ) * m) ^ (pExp - 1)⌉₊ : ℕ) := by
        rw [paramB, if_neg hsm]
      rw [hM, hB'] at hrm
      obtain ⟨mR, hmR⟩ : ∃ mR : ℝ, mR = ((⌈c * ((κ:ℝ) * m) ^ (pExp - 1)⌉₊ : ℕ) : ℝ) := ⟨_, rfl⟩
      rw [← hmR] at hrm
      have hκ1 : (1:ℝ) ≤ κ := by exact_mod_cast hκ
      have hu : 1 ≤ (κ:ℝ) * m := by nlinarith
      have hpp : 0 ≤ pExp - 1 := by linarith
      have hupow : 1 ≤ ((κ:ℝ) * m) ^ (pExp - 1) := Real.one_le_rpow hu hpp
      have hinner0 : 0 ≤ c * ((κ:ℝ) * m) ^ (pExp - 1) := by positivity
      have hmlow : c * ((κ:ℝ) * m) ^ (pExp - 1) ≤ mR := hmR ▸ Nat.le_ceil _
      have hmup : mR < c * ((κ:ℝ) * m) ^ (pExp - 1) + 1 := hmR ▸ Nat.ceil_lt_add_one hinner0
      have hm2R : 2 ≤ mR := by
        nlinarith [mul_le_mul_of_nonneg_left hupow (by linarith : (0:ℝ) ≤ c)]
      have hmRpos : 0 < mR := by linarith
      have hκ4 : (κ:ℝ) ^ 4 ≤ m := by
        push_neg at hsm
        have : (κ:ℝ) ^ 4 ≤ B * (κ:ℝ) ^ 4 :=
          le_mul_of_one_le_left (by positivity) hB
        linarith
      have hκq : (κ:ℝ) ≤ (m:ℝ) ^ (((4:ℕ):ℝ)⁻¹) := by
        have h := Real.rpow_le_rpow (by positivity) hκ4 (by positivity : (0:ℝ) ≤ ((4:ℕ):ℝ)⁻¹)
        rwa [Real.pow_rpow_inv_natCast (by positivity) (by norm_num)] at h
      have hκN : (κ:ℝ) * m ≤ (m:ℝ) ^ ((5:ℝ) / 4) := by
        have : (m:ℝ) ^ ((5:ℝ) / 4) = (m:ℝ) ^ (((4:ℕ):ℝ)⁻¹) * m := by
          rw [show ((5:ℝ) / 4) = ((4:ℕ):ℝ)⁻¹ + 1 by norm_num, Real.rpow_add hmpos, Real.rpow_one]
        rw [this]; exact mul_le_mul_of_nonneg_right hκq hmpos.le
      have hκNp : ((κ:ℝ) * m) ^ (pExp - 1) ≤ (m:ℝ) ^ ((5:ℝ) / 4 * (pExp - 1)) := by
        rw [Real.rpow_mul hmpos.le]
        exact Real.rpow_le_rpow (by positivity) hκN hpp
      obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (m:ℝ) / mR := ⟨_, rfl⟩
      rw [← hx] at hrm
      have hx0 : 0 < x := hx ▸ div_pos hmpos hmRpos
      have hxN : x ≤ m := hx ▸ div_le_self hmpos.le (by linarith)
      have hxhalf : x ≤ (m:ℝ) / 2 := hx ▸ div_le_div_of_nonneg_left hmpos.le (by norm_num) hm2R
      have hRx : R ⌈x⌉₊ ≤ 1 + 4 * A₀ * x := by
        rcases le_or_gt x 1 with hx1 | hx1
        · have : ⌈x⌉₊ = 1 :=
            le_antisymm (Nat.ceil_le.2 (by simpa using hx1)) (Nat.one_le_ceil_iff.2 hx0)
          rw [this]
          have : 0 ≤ 4 * A₀ * x := by positivity
          linarith
        · have h1 : 1 ≤ ⌈x⌉₊ := Nat.one_le_ceil_iff.2 hx0
          have h2 : ⌈x⌉₊ ≤ 2 ^ k' := by
            rw [Nat.ceil_le]; push_cast; linarith
          have h3 := hlin _ h1 h2
          have h4 : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0.le
          have h5 : (⌈x⌉₊ : ℝ) ≤ 2 * x := by linarith
          have h6 := mul_le_mul_of_nonneg_left h5 (by linarith : (0:ℝ) ≤ 2 * A₀)
          linarith
      have hsplitN : (m:ℝ) ^ (2 - pExp) * (m:ℝ) ^ (pExp - 1) = m := by
        rw [← Real.rpow_add hmpos, show 2 - pExp + (pExp - 1) = (1:ℝ) by ring, Real.rpow_one]
      have hmlow2 : c * (m:ℝ) ^ (pExp - 1) ≤ mR := by
        refine le_trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hmpos.le (le_mul_of_one_le_left hmpos.le hκ1) hpp) (by linarith)) hmlow
      have h2p0 : 0 ≤ (m:ℝ) ^ (2 - pExp) := by positivity
      have hxc : x * c ≤ (m:ℝ) ^ (2 - pExp) := by
        rw [hx, div_mul_eq_mul_div, div_le_iff₀ hmRpos]
        calc (m:ℝ) * c = c * ((m:ℝ) ^ (2 - pExp) * (m:ℝ) ^ (pExp - 1)) := by rw [hsplitN]; ring
          _ = (m:ℝ) ^ (2 - pExp) * (c * (m:ℝ) ^ (pExp - 1)) := by ring
          _ ≤ (m:ℝ) ^ (2 - pExp) * mR := mul_le_mul_of_nonneg_left hmlow2 h2p0
      have hx13N : x ^ ((1:ℝ) / 3) ≤ (m:ℝ) ^ ((1:ℝ) / 3) := Real.rpow_le_rpow hx0.le hxN (by norm_num)
      have hx13 : x ^ ((1:ℝ) / 3) ≤ (m:ℝ) ^ ((2 - pExp) / 3) := by
        have hxle : x ≤ (m:ℝ) ^ (2 - pExp) := by nlinarith
        calc x ^ ((1:ℝ) / 3) ≤ ((m:ℝ) ^ (2 - pExp)) ^ ((1:ℝ) / 3) :=
              Real.rpow_le_rpow hx0.le hxle (by norm_num)
          _ = (m:ℝ) ^ ((2 - pExp) / 3) := by rw [← Real.rpow_mul hmpos.le]; congr 1; ring
      have hy0 : 0 ≤ x ^ ((1:ℝ) / 3) := by positivity
      have hz : x ^ ((1:ℝ) / 3) * x * c ≤ (m:ℝ) ^ ((19:ℝ) / 20) := by
        calc x ^ ((1:ℝ) / 3) * x * c = x ^ ((1:ℝ) / 3) * (x * c) := by ring
          _ ≤ (m:ℝ) ^ ((2 - pExp) / 3) * (m:ℝ) ^ (2 - pExp) :=
              mul_le_mul hx13 hxc (by positivity) (by positivity)
          _ = (m:ℝ) ^ ((2 - pExp) / 3 + (2 - pExp)) := by rw [Real.rpow_add hmpos]
          _ ≤ (m:ℝ) ^ ((19:ℝ) / 20) := Real.rpow_le_rpow_of_exponent_le hm1R (by linarith)
      have hw : x ^ ((1:ℝ) / 3) * (mR + 1) ≤ (c + 2) * (m:ℝ) ^ ((19:ℝ) / 20) := by
        have hE : 1 ≤ (m:ℝ) ^ ((5:ℝ) / 4 * (pExp - 1)) := Real.one_le_rpow hm1R (by nlinarith)
        have hcE := mul_le_mul_of_nonneg_left hκNp (by linarith : (0:ℝ) ≤ c)
        have hmR' : mR + 1 ≤ (c + 2) * (m:ℝ) ^ ((5:ℝ) / 4 * (pExp - 1)) := by nlinarith
        calc x ^ ((1:ℝ) / 3) * (mR + 1)
            ≤ (m:ℝ) ^ ((1:ℝ) / 3) * ((c + 2) * (m:ℝ) ^ ((5:ℝ) / 4 * (pExp - 1))) :=
              mul_le_mul hx13N hmR' (by linarith) (by positivity)
          _ = (c + 2) * (m:ℝ) ^ ((1:ℝ) / 3 + (5:ℝ) / 4 * (pExp - 1)) := by
              rw [Real.rpow_add hmpos]; ring
          _ ≤ (c + 2) * (m:ℝ) ^ ((19:ℝ) / 20) := mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hm1R (by linarith)) (by linarith)
      set Q := (2:ℝ) ^ ((19:ℝ) / 20 * k') with hQ
      have hQ0 : 0 ≤ Q := by linarith
      have ht1 : C₀ * x ^ ((1:ℝ) / 3) * (mR + R ⌈x⌉₊) ≤
          C₀ * (x ^ ((1:ℝ) / 3) * (mR + 1)) + 4 * A₀ * C₀ * (x ^ ((1:ℝ) / 3) * x) := by
        have := mul_le_mul_of_nonneg_left hRx (mul_nonneg hC₀.le hy0)
        nlinarith
      have ha : C₀ * (x ^ ((1:ℝ) / 3) * (mR + 1)) ≤ A₀ * g * Q / 4 := by
        calc C₀ * (x ^ ((1:ℝ) / 3) * (mR + 1)) ≤ C₀ * ((c + 2) * (m:ℝ) ^ ((19:ℝ) / 20)) :=
              mul_le_mul_of_nonneg_left hw hC₀.le
          _ ≤ C₀ * ((c + 2) * (2 * Q)) := mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hNθ (by linarith)) hC₀.le
          _ = (8 * C₀ * (c + 2)) * Q / 4 := by ring
          _ ≤ (A₀ * g) * Q / 4 := by
              have := mul_le_mul_of_nonneg_right hAg hQ0
              linarith
      have hb : 4 * A₀ * C₀ * (x ^ ((1:ℝ) / 3) * x) ≤ A₀ * g * Q / 4 := by
        have hzQ : x ^ ((1:ℝ) / 3) * x * c ≤ 2 * Q := le_trans hz hNθ
        have hk : 0 ≤ 4 * A₀ * C₀ := by positivity
        have : (4 * A₀ * C₀ * (x ^ ((1:ℝ) / 3) * x)) * c ≤ (A₀ * g * Q / 4) * c := by
          calc (4 * A₀ * C₀ * (x ^ ((1:ℝ) / 3) * x)) * c
              = 4 * A₀ * C₀ * (x ^ ((1:ℝ) / 3) * x * c) := by ring
            _ ≤ 4 * A₀ * C₀ * (2 * Q) := mul_le_mul_of_nonneg_left hzQ hk
            _ = A₀ * Q / 4 * (32 * C₀) := by ring
            _ ≤ A₀ * Q / 4 * (c * g) :=
                mul_le_mul_of_nonneg_left hcg (by positivity)
            _ = (A₀ * g * Q / 4) * c := by ring
        exact le_of_mul_le_mul_right this (by linarith)
      linarith
  intro n hn
  have h1 := key (Nat.clog 2 n) n hn (Nat.le_pow_clog (by norm_num) n)
  have h2 := hΨle (Nat.clog 2 n)
  have h3 := mul_le_mul_of_nonneg_left (hclog n hn) hA0.le
  linarith
