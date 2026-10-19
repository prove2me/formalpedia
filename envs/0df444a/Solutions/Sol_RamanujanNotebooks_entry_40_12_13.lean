-- Prove2me | solution 1 for RamanujanNotebooks.entry_40_12_13
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T15:18:27.416103+00:00
-- url     : https://prove2.me/submissions/88dcf83a-cb7b-43c3-a4ab-b1b6adbea3ec

import Mathlib
import Definitions.Def_RamanujanNotebooks_shared_shiftedFactorial
import Definitions.Def_RamanujanNotebooks_shared_hypPFQTerm

namespace RNE40
open RamanujanNotebooks Filter Topology Complex

lemma poch_succ (s : ℂ) (k : ℕ) : shiftedFactorial s (k + 1) = shiftedFactorial s k * (s + k) := by
  simp [shiftedFactorial, Finset.prod_range_succ]

lemma poch_eq (s : ℂ) (k : ℕ) (hG : GammaSeq s k ≠ 0) :
    shiftedFactorial s (k + 1) = (k : ℂ) ^ s * (k.factorial : ℂ) / GammaSeq s k := by
  have hP : ∏ j ∈ Finset.range (k + 1), (s + j) ≠ 0 := by
    intro h; apply hG; simp [GammaSeq, h]
  have hN : (k : ℂ) ^ s * (k.factorial : ℂ) ≠ 0 := by
    intro h; apply hG; simp [GammaSeq, h]
  unfold GammaSeq
  simp only [shiftedFactorial]
  field_simp
  rw [div_self hN]

lemma norm_cpow_nat (k : ℕ) (hk : 1 ≤ k) (s : ℂ) : ‖(k : ℂ) ^ s‖ = (k : ℝ) ^ s.re :=
  Complex.norm_natCast_cpow_of_pos (by omega) s

/-- lower bound for a Pochhammer symbol that never vanishes -/
lemma lower (s : ℂ) (hs : ∀ k, shiftedFactorial s k ≠ 0) :
    ∃ c > 0, ∀ᶠ k : ℕ in atTop, c * ((k : ℝ) ^ s.re * k.factorial) ≤ ‖shiftedFactorial s (k + 1)‖ := by
  have hpole : ∀ m : ℕ, s ≠ -m := by
    intro m h
    apply hs (m + 1)
    rw [poch_succ, h]; simp
  have hΓ := Complex.Gamma_ne_zero hpole
  have hT := Complex.GammaSeq_tendsto_Gamma s
  have hpos : 0 < ‖Gamma s‖ := norm_pos_iff.mpr hΓ
  have hev : ∀ᶠ k : ℕ in atTop, ‖GammaSeq s k‖ < 2 * ‖Gamma s‖ ∧ ‖Gamma s‖ / 2 < ‖GammaSeq s k‖ := by
    have h1 := (continuous_norm.tendsto _).comp hT
    have := h1.eventually (Ioo_mem_nhds (show ‖Gamma s‖ / 2 < ‖Gamma s‖ by linarith)
      (show ‖Gamma s‖ < 2 * ‖Gamma s‖ by linarith))
    filter_upwards [this] with k hk
    exact ⟨hk.2, hk.1⟩
  refine ⟨1 / (2 * ‖Gamma s‖), by positivity, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with k hk hk1
  have hG : GammaSeq s k ≠ 0 := by
    intro h; rw [h, norm_zero] at hk; linarith [hk.2]
  rw [poch_eq s k hG, norm_div, norm_mul, norm_cpow_nat k hk1, Complex.norm_natCast]
  rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (norm_pos_iff.mpr hG)]
  have : 0 ≤ (k : ℝ) ^ s.re * k.factorial := by positivity
  nlinarith [hk.1]

/-- upper bound when `s` is not a pole -/
lemma upper (s : ℂ) (hpole : ∀ m : ℕ, s ≠ -m) :
    ∃ C, ∀ᶠ k : ℕ in atTop, ‖shiftedFactorial s (k + 1)‖ ≤ C * ((k : ℝ) ^ s.re * k.factorial) := by
  have hΓ := Complex.Gamma_ne_zero hpole
  have hT := Complex.GammaSeq_tendsto_Gamma s
  have hpos : 0 < ‖Gamma s‖ := norm_pos_iff.mpr hΓ
  have hev : ∀ᶠ k : ℕ in atTop, ‖Gamma s‖ / 2 < ‖GammaSeq s k‖ := by
    have h1 := (continuous_norm.tendsto _).comp hT
    exact h1.eventually (Ioi_mem_nhds (show ‖Gamma s‖ / 2 < ‖Gamma s‖ by linarith))
  refine ⟨2 / ‖Gamma s‖, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with k hk hk1
  have hG : GammaSeq s k ≠ 0 := by
    intro h; rw [h, norm_zero] at hk; linarith
  rw [poch_eq s k hG, norm_div, norm_mul, norm_cpow_nat k hk1, Complex.norm_natCast]
  rw [div_le_iff₀ (norm_pos_iff.mpr hG)]
  have : 0 ≤ (k : ℝ) ^ s.re * k.factorial := by positivity
  have h2 : 2 / ‖Gamma s‖ * ‖GammaSeq s k‖ ≥ 1 := by
    rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ hpos]; linarith
  nlinarith

/-- a pole: the Pochhammer symbol vanishes eventually -/
lemma pole_zero (s : ℂ) (m : ℕ) (hs : s = -m) : ∀ k, m < k → shiftedFactorial s k = 0 := by
  intro k hk
  unfold shiftedFactorial
  apply Finset.prod_eq_zero (i := m) (Finset.mem_range.mpr hk)
  rw [hs]; ring

lemma sf_zero (s : ℂ) : shiftedFactorial s 0 = 1 := by simp [shiftedFactorial]

lemma sf_one_eq (k : ℕ) : shiftedFactorial 1 k = (k.factorial : ℂ) := by
  induction k with
  | zero => simp [sf_zero]
  | succ k ih => rw [poch_succ, ih, Nat.factorial_succ]; push_cast; ring

lemma sf_shift (a : ℂ) (k : ℕ) : shiftedFactorial (a + 1) k * a = shiftedFactorial a k * (a + k) := by
  induction k with
  | zero => simp [sf_zero]
  | succ k ih =>
    rw [poch_succ, poch_succ, mul_right_comm, ih]; push_cast; ring

section
variable (n x : ℂ)

noncomputable def R (K : ℕ) : ℂ :=
  shiftedFactorial (-x) K * (K.factorial : ℂ) * (n + K - 1) * (x + n + K) /
    ((x + n - 1) * shiftedFactorial n K * shiftedFactorial (x + n + 1) K)

noncomputable def t (k : ℕ) : ℂ :=
  (n + 2 * k) * (k.factorial : ℂ) * shiftedFactorial (-x) k /
    (shiftedFactorial n k * shiftedFactorial (x + n + 1) k)

lemma t_eq (hn2 : ∀ k : ℕ, shiftedFactorial (n / 2) k ≠ 0) (hnn : ∀ k : ℕ, shiftedFactorial n k ≠ 0)
    (hd : ∀ k : ℕ, shiftedFactorial (x + n + 1) k ≠ 0) (k : ℕ) :
    n * hypPFQTerm [n / 2 + 1, 1, 1, -x] [n / 2, n, x + n + 1] 1 k = t n x k := by
  have h := sf_shift (n / 2) k
  simp only [hypPFQTerm, List.map, List.prod_cons, List.prod_nil, sf_one_eq, one_pow, mul_one, t]
  have h2 := hn2 k
  have h3 := hnn k
  have h4 := hd k
  have h5 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  generalize shiftedFactorial (n / 2 + 1) k = B at h ⊢
  generalize shiftedFactorial (n / 2) k = A at h h2 ⊢
  generalize shiftedFactorial n k = N at h3 ⊢
  generalize shiftedFactorial (x + n + 1) k = Y at h4 ⊢
  generalize shiftedFactorial (-x) k = X
  generalize (k.factorial : ℂ) = F at h5 ⊢
  rw [mul_div_assoc', div_eq_div_iff (mul_ne_zero (mul_ne_zero h2 (mul_ne_zero h3 h4)) h5)
    (mul_ne_zero h3 h4)]
  linear_combination (2 * F * F * X * N * Y) * h

lemma tele (hx : x + n - 1 ≠ 0) (hnn : ∀ k : ℕ, shiftedFactorial n k ≠ 0)
    (hd : ∀ k : ℕ, shiftedFactorial (x + n + 1) k ≠ 0) (K : ℕ) :
    t n x K = R n x K - R n x (K + 1) := by
  have a1 := hnn (K + 1)
  have a2 := hd (K + 1)
  rw [poch_succ] at a1 a2
  have hN := hnn K
  have hY := hd K
  have hn' : n + K ≠ 0 := right_ne_zero_of_mul a1
  have hy' : x + n + 1 + K ≠ 0 := right_ne_zero_of_mul a2
  unfold R t
  rw [poch_succ (-x), poch_succ n, poch_succ (x + n + 1), Nat.factorial_succ]
  push_cast
  generalize shiftedFactorial n K = N at hN ⊢
  generalize shiftedFactorial (x + n + 1) K = Y at hY ⊢
  generalize shiftedFactorial (-x) K = X
  generalize (K.factorial : ℂ) = F
  have e : (n + 2 * K) = ((n + K - 1) * (x + n + K) - (-x + K) * (K + 1)) / (x + n - 1) := by
    field_simp; ring
  rw [e]
  field_simp
  ring

lemma partial_sum (hx : x + n - 1 ≠ 0) (hnn : ∀ k : ℕ, shiftedFactorial n k ≠ 0)
    (hd : ∀ k : ℕ, shiftedFactorial (x + n + 1) k ≠ 0) (K : ℕ) :
    ∑ k ∈ Finset.range K, t n x k = R n x 0 - R n x K := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ, ih, tele n x hx hnn hd K]; ring

lemma R_zero (hx : x + n - 1 ≠ 0) : R n x 0 = (n - 1) * (x + n) / (x + n - 1) := by
  simp [R, sf_zero]

end

lemma rpow_rel (k : ℕ) (hk : 1 ≤ k) (a b c : ℝ) :
    (k : ℝ) ^ a * (k : ℝ) ^ b = (k : ℝ) ^ (a + b) ∧ (k : ℝ) ^ c = (k : ℝ) ^ c := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  exact ⟨(Real.rpow_add hk0 a b).symm, rfl⟩

lemma kpow (k : ℕ) (hk : 1 ≤ k) (a b : ℝ) : (k : ℝ) ^ a * (k : ℝ) ^ b = (k : ℝ) ^ (a + b) :=
  (rpow_rel k hk a b 0).1

lemma kpow_nat (k : ℕ) (hk : 1 ≤ k) (m : ℕ) : (k : ℝ) ^ m = (k : ℝ) ^ (m : ℝ) :=
  (Real.rpow_natCast _ _).symm

theorem main (n x : ℂ) (h : 1 < (x + n).re)
    (hn : ∀ k : ℕ, shiftedFactorial (n / 2) k ≠ 0)
    (hd : ∀ k : ℕ, shiftedFactorial (x + n + 1) k ≠ 0)
    (hnn : ∀ k : ℕ, shiftedFactorial n k ≠ 0) :
    HasSum (fun k : ℕ => n * hypPFQTerm [n / 2 + 1, 1, 1, -x] [n / 2, n, x + n + 1] (1) k)
      ((n - 1) * (x + n) / (x + n - 1)) := by
  have hx1 : x + n - 1 ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp at this; simp only [Complex.add_re] at h; linarith
  simp_rw [t_eq n x hn hnn hd]
  -- summability and vanishing of R
  have key : Summable (t n x) ∧ Tendsto (R n x) atTop (𝓝 0) := by
    by_cases hp : ∃ m : ℕ, -x = -(m : ℂ)
    · obtain ⟨m, hm⟩ := hp
      have hz := pole_zero (-x) m hm
      constructor
      · apply summable_of_ne_finset_zero (s := Finset.range (m + 1))
        intro k hk
        rw [Finset.mem_range, not_lt] at hk
        simp [t, hz k (by omega)]
      · apply tendsto_const_nhds.congr'
        filter_upwards [eventually_gt_atTop m] with k hk
        simp [R, hz k hk]
    · push Not at hp
      obtain ⟨C0, hC0⟩ := upper (-x) hp
      obtain ⟨c1, hc1, hl1⟩ := lower n hnn
      obtain ⟨c2, hc2, hl2⟩ := lower (x + n + 1) hd
      set σ := (x + n).re with hσ
      have hre1 : (-x).re = -x.re := by simp
      have hre2 : (x + n + 1).re = x.re + n.re + 1 := by simp
      have hσ' : σ = x.re + n.re := by simp [hσ]
      constructor
      · -- summability
        set M : ℝ := 2 * (‖n‖ + 4)
        have hbound : ∀ᶠ k : ℕ in atTop, ‖t n x (k + 1)‖ ≤
            (M * C0 / (c1 * c2)) * (k : ℝ) ^ (1 - 2 * σ) := by
          filter_upwards [hC0, hl1, hl2, eventually_ge_atTop 1] with k hX hN hY hk
          have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
          have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
          rw [hre1] at hX; rw [hre2] at hY
          set F : ℝ := (k.factorial : ℝ)
          have hF : 0 < F := by positivity
          set a := (k : ℝ) ^ (-x.re)
          set b := (k : ℝ) ^ n.re
          set c := (k : ℝ) ^ (x.re + n.re + 1)
          set d := (k : ℝ) ^ (1 - 2 * σ)
          have ha : 0 < a := Real.rpow_pos_of_pos hk0 _
          have hb : 0 < b := Real.rpow_pos_of_pos hk0 _
          have hc : 0 < c := Real.rpow_pos_of_pos hk0 _
          have hdd : 0 < d := Real.rpow_pos_of_pos hk0 _
          have hrel : d * b * c = (k : ℝ) ^ 2 * a := by
            simp only [d, b, c, a]
            rw [kpow k hk, kpow k hk, kpow_nat k hk, kpow k hk, hσ']
            congr 1; push_cast; ring
          have hNpos : 0 < ‖shiftedFactorial n (k + 1)‖ := norm_pos_iff.mpr (hnn _)
          have hYpos : 0 < ‖shiftedFactorial (x + n + 1) (k + 1)‖ := norm_pos_iff.mpr (hd _)
          have hC0nn : 0 ≤ C0 := by
            by_contra hneg; push Not at hneg
            have : C0 * (a * F) < 0 := mul_neg_of_neg_of_pos hneg (by positivity)
            linarith [norm_nonneg (shiftedFactorial (-x) (k + 1))]
          have hnorm1 : ‖n + 2 * ((k + 1 : ℕ) : ℂ)‖ ≤ ‖n‖ + 2 * k + 2 := by
            calc ‖n + 2 * ((k + 1 : ℕ) : ℂ)‖ ≤ ‖n‖ + ‖2 * ((k + 1 : ℕ) : ℂ)‖ := norm_add_le _ _
              _ = ‖n‖ + 2 * k + 2 := by
                rw [norm_mul, Complex.norm_natCast]; push_cast; simp; ring
          have hM : (‖n‖ + 2 * k + 2) * (k + 1) ≤ M * (k : ℝ) ^ 2 := by
            simp only [M]
            have hn0 := norm_nonneg n
            have e1 : ‖n‖ * (k + 1) ≤ 2 * ‖n‖ * (k : ℝ) ^ 2 := by
              have : (k : ℝ) + 1 ≤ 2 * (k : ℝ) ^ 2 := by nlinarith
              nlinarith
            have e2 : 2 * (k : ℝ) ^ 2 + 4 * k + 2 ≤ 8 * (k : ℝ) ^ 2 := by nlinarith
            nlinarith
          unfold t
          rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_natCast,
            div_le_iff₀ (mul_pos hNpos hYpos), Nat.factorial_succ]
          push_cast
          calc ‖n + 2 * ((k : ℂ) + 1)‖ * ((k + 1) * F) * ‖shiftedFactorial (-x) (k + 1)‖
              ≤ (‖n‖ + 2 * k + 2) * ((k + 1) * F) * (C0 * (a * F)) := by
                have := hnorm1; push_cast at this
                gcongr
            _ = ((‖n‖ + 2 * k + 2) * (k + 1)) * C0 * a * F * F := by ring
            _ ≤ (M * (k : ℝ) ^ 2) * C0 * a * F * F := by gcongr
            _ = (M * C0 / (c1 * c2)) * d * (c1 * (b * F)) * (c2 * (c * F)) := by
                rw [show M * (k : ℝ) ^ 2 * C0 * a * F * F = M * C0 * F * F * ((k : ℝ) ^ 2 * a) by ring,
                  ← hrel]
                field_simp
            _ ≤ (M * C0 / (c1 * c2)) * d * ‖shiftedFactorial n (k + 1)‖ *
                  ‖shiftedFactorial (x + n + 1) (k + 1)‖ := by
                gcongr
            _ = _ := by ring
        have hs : Summable (fun k : ℕ => (M * C0 / (c1 * c2)) * (k : ℝ) ^ (1 - 2 * σ)) :=
          (Real.summable_nat_rpow.mpr (by linarith)).mul_left _
        have h1 : Summable (fun k : ℕ => t n x (k + 1)) :=
          Summable.of_norm_bounded_eventually_nat hs hbound
        exact (summable_nat_add_iff 1).mp h1
      · -- R → 0
        set M : ℝ := 2 * (‖n‖ + 1) * (‖x + n‖ + 2)
        have hbound : ∀ᶠ k : ℕ in atTop, ‖R n x (k + 1)‖ ≤
            (M * C0 / (‖x + n - 1‖ * c1 * c2)) * (k : ℝ) ^ (2 - 2 * σ) := by
          filter_upwards [hC0, hl1, hl2, eventually_ge_atTop 1] with k hX hN hY hk
          have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
          have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
          rw [hre1] at hX; rw [hre2] at hY
          set F : ℝ := (k.factorial : ℝ)
          have hF : 0 < F := by positivity
          set a := (k : ℝ) ^ (-x.re)
          set b := (k : ℝ) ^ n.re
          set c := (k : ℝ) ^ (x.re + n.re + 1)
          set d := (k : ℝ) ^ (2 - 2 * σ)
          have ha : 0 < a := Real.rpow_pos_of_pos hk0 _
          have hb : 0 < b := Real.rpow_pos_of_pos hk0 _
          have hc : 0 < c := Real.rpow_pos_of_pos hk0 _
          have hdd : 0 < d := Real.rpow_pos_of_pos hk0 _
          have hrel : d * b * c = (k : ℝ) ^ 3 * a := by
            simp only [d, b, c, a]
            rw [kpow k hk, kpow k hk, kpow_nat k hk, kpow k hk, hσ']
            congr 1; push_cast; ring
          have hNpos : 0 < ‖shiftedFactorial n (k + 1)‖ := norm_pos_iff.mpr (hnn _)
          have hYpos : 0 < ‖shiftedFactorial (x + n + 1) (k + 1)‖ := norm_pos_iff.mpr (hd _)
          have hx1p : 0 < ‖x + n - 1‖ := norm_pos_iff.mpr hx1
          have hC0nn : 0 ≤ C0 := by
            by_contra hneg; push Not at hneg
            have : C0 * (a * F) < 0 := mul_neg_of_neg_of_pos hneg (by positivity)
            linarith [norm_nonneg (shiftedFactorial (-x) (k + 1))]
          have hn1 : ‖n + ((k + 1 : ℕ) : ℂ) - 1‖ ≤ ‖n‖ + k := by
            calc ‖n + ((k + 1 : ℕ) : ℂ) - 1‖ = ‖n + (k : ℂ)‖ := by push_cast; ring_nf
              _ ≤ ‖n‖ + ‖(k : ℂ)‖ := norm_add_le _ _
              _ = ‖n‖ + k := by rw [Complex.norm_natCast]
          have hn2 : ‖x + n + ((k + 1 : ℕ) : ℂ)‖ ≤ ‖x + n‖ + k + 1 := by
            calc ‖x + n + ((k + 1 : ℕ) : ℂ)‖ ≤ ‖x + n‖ + ‖((k + 1 : ℕ) : ℂ)‖ := norm_add_le _ _
              _ = ‖x + n‖ + k + 1 := by rw [Complex.norm_natCast]; push_cast; ring
          have hM : (k + 1) * (‖n‖ + k) * (‖x + n‖ + k + 1) ≤ M * (k : ℝ) ^ 3 := by
            simp only [M]
            have h1' : (k : ℝ) + 1 ≤ 2 * k := by linarith
            have h2' : ‖n‖ + k ≤ (‖n‖ + 1) * k := by nlinarith [norm_nonneg n]
            have h3' : ‖x + n‖ + k + 1 ≤ (‖x + n‖ + 2) * k := by nlinarith [norm_nonneg (x + n)]
            calc (k + 1) * (‖n‖ + k) * (‖x + n‖ + k + 1)
                ≤ (2 * k) * ((‖n‖ + 1) * k) * ((‖x + n‖ + 2) * k) := by gcongr
              _ = _ := by ring
          unfold R
          rw [norm_div, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_natCast,
            div_le_iff₀ (mul_pos (mul_pos hx1p hNpos) hYpos), Nat.factorial_succ]
          push_cast
          have hn1' := hn1; have hn2' := hn2
          push_cast at hn1' hn2'
          calc ‖shiftedFactorial (-x) (k + 1)‖ * ((k + 1) * F) * ‖n + ((k : ℂ) + 1) - 1‖ *
                ‖x + n + ((k : ℂ) + 1)‖
              ≤ (C0 * (a * F)) * ((k + 1) * F) * (‖n‖ + k) * (‖x + n‖ + k + 1) := by gcongr
            _ = ((k + 1) * (‖n‖ + k) * (‖x + n‖ + k + 1)) * C0 * a * F * F := by ring
            _ ≤ (M * (k : ℝ) ^ 3) * C0 * a * F * F := by gcongr
            _ = (M * C0 / (‖x + n - 1‖ * c1 * c2)) * d * ‖x + n - 1‖ * (c1 * (b * F)) * (c2 * (c * F)) := by
                rw [show M * (k : ℝ) ^ 3 * C0 * a * F * F = M * C0 * F * F * ((k : ℝ) ^ 3 * a) by ring,
                  ← hrel]
                field_simp
            _ ≤ (M * C0 / (‖x + n - 1‖ * c1 * c2)) * d * ‖x + n - 1‖ * ‖shiftedFactorial n (k + 1)‖ *
                  ‖shiftedFactorial (x + n + 1) (k + 1)‖ := by
                gcongr
            _ = _ := by ring
        have hlim : Tendsto (fun k : ℕ => (M * C0 / (‖x + n - 1‖ * c1 * c2)) * (k : ℝ) ^ (2 - 2 * σ))
            atTop (𝓝 0) := by
          have h1 : Tendsto (fun k : ℕ => (k : ℝ) ^ (2 - 2 * σ)) atTop (𝓝 0) := by
            have := (tendsto_rpow_neg_atTop (show 0 < 2 * σ - 2 by linarith)).comp
              tendsto_natCast_atTop_atTop
            simpa [Function.comp_def, neg_sub] using this
          simpa using h1.const_mul (M * C0 / (‖x + n - 1‖ * c1 * c2))
        have h2 : Tendsto (fun k : ℕ => R n x (k + 1)) atTop (𝓝 0) :=
          squeeze_zero_norm' hbound hlim
        exact (tendsto_add_atTop_iff_nat 1).mp h2
  obtain ⟨hsum, hR⟩ := key
  rw [hsum.hasSum_iff_tendsto_nat]
  simp_rw [partial_sum n x hx1 hnn hd]
  rw [← R_zero n x hx1]
  simpa using (tendsto_const_nhds (x := R n x 0)).sub hR

end RNE40

open RamanujanNotebooks in
theorem solution (n x : ℂ) (h : 1 < (x + n).re)
    (hn : ∀ k : ℕ, shiftedFactorial (n / 2) k ≠ 0)
    (hd : ∀ k : ℕ, shiftedFactorial (x + n + 1) k ≠ 0)
    (hnn : ∀ k : ℕ, shiftedFactorial n k ≠ 0) :
    HasSum (fun k : ℕ => n * hypPFQTerm [n / 2 + 1, 1, 1, -x] [n / 2, n, x + n + 1] (1) k) ((n - 1) * (x + n) / (x + n - 1)) :=
  RNE40.main n x h hn hd hnn
