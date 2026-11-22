-- Prove2me | solution 1 for ParallelSU2.Reduction.buzek_optimum
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-22T15:15:02.957514+00:00
-- url     : https://prove2.me/submissions/2c76bc60-8c83-416b-befb-66a02c5ad81d

import Mathlib

open Filter Topology

set_option maxHeartbeats 800000

theorem solution :
    (∀ n : ℕ, IsLeast
      {v : ℝ | ∃ a : Fin (n + 1) → ℝ, (∀ k, 0 ≤ a k) ∧ ∑ k, a k ^ 2 = 1 ∧
        v = (1 / 2 : ℝ) * (1 - ∑ k : Fin n, a k.castSucc * a k.succ)}
      (Real.sin (Real.pi / (2 * ((n : ℝ) + 2))) ^ 2)) ∧
    Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * Real.sin (Real.pi / (2 * ((n : ℝ) + 2))) ^ 2) atTop
      (𝓝 (Real.pi ^ 2 / 4)) := by
  have key_abstract : ∀ (nn : ℕ), 1 ≤ nn → ∀ (s : ℕ → ℝ) (c : ℝ),
      (∀ k ≤ nn, 0 < s k) →
      (∀ k, 1 ≤ k → k < nn → s (k + 1) + s (k - 1) = 2 * c * s k) →
      s 1 = 2 * c * s 0 →
      s (nn - 1) = 2 * c * s nn →
      (∑ k ∈ Finset.range nn, s k * s (k + 1) = c * ∑ k ∈ Finset.range (nn + 1), s k ^ 2) ∧
      (∀ a : ℕ → ℝ,
        ∑ k ∈ Finset.range nn, a k * a (k + 1) ≤ c * ∑ k ∈ Finset.range (nn + 1), a k ^ 2) := by
    intro nn hnn s c hs_pos hrec hb0 hbn
    have hpt : ∀ a : ℕ → ℝ, ∀ k ∈ Finset.range nn,
        (a k * s (k + 1) - a (k + 1) * s k) ^ 2 / (s k * s (k + 1))
          = a k ^ 2 * (s (k + 1) / s k) - 2 * (a k * a (k + 1))
            + a (k + 1) ^ 2 * (s k / s (k + 1)) := by
      intro a k hk
      have hk' : k < nn := Finset.mem_range.mp hk
      have h1 : s k ≠ 0 := (hs_pos k (by omega)).ne'
      have h2 : s (k + 1) ≠ 0 := (hs_pos (k + 1) (by omega)).ne'
      field_simp
      ring
    have key_id : ∀ a : ℕ → ℝ,
        2 * c * (∑ k ∈ Finset.range (nn + 1), a k ^ 2)
            - 2 * (∑ k ∈ Finset.range nn, a k * a (k + 1))
          = ∑ k ∈ Finset.range nn,
              (a k * s (k + 1) - a (k + 1) * s k) ^ 2 / (s k * s (k + 1)) := by
      intro a
      rw [Finset.sum_congr rfl (hpt a)]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      have hGsplit : (∑ k ∈ Finset.range nn, a k ^ 2 * (s (k + 1) / s k))
          = a 0 ^ 2 * (s 1 / s 0)
            + ∑ k ∈ Finset.range (nn - 1), a (k + 1) ^ 2 * (s (k + 1 + 1) / s (k + 1)) := by
        have hn : nn = (nn - 1) + 1 := by omega
        conv_lhs => rw [hn]
        rw [Finset.sum_range_succ']
        ring
      have hHsplit : (∑ k ∈ Finset.range nn, a (k + 1) ^ 2 * (s k / s (k + 1)))
          = (∑ k ∈ Finset.range (nn - 1), a (k + 1) ^ 2 * (s k / s (k + 1)))
            + a nn ^ 2 * (s (nn - 1) / s nn) := by
        have hn : nn = (nn - 1) + 1 := by omega
        conv_lhs => rw [hn]
        rw [Finset.sum_range_succ]
        rw [Nat.sub_add_cancel hnn]
      have ht2 : (∑ k ∈ Finset.range nn, 2 * (a k * a (k + 1)))
          = 2 * ∑ k ∈ Finset.range nn, a k * a (k + 1) := by
        rw [Finset.mul_sum]
      have hmidpt : ∀ k ∈ Finset.range (nn - 1),
          a (k + 1) ^ 2 * (s (k + 1 + 1) / s (k + 1)) + a (k + 1) ^ 2 * (s k / s (k + 1))
            = 2 * c * a (k + 1) ^ 2 := by
        intro k hk
        have hk' : k < nn - 1 := Finset.mem_range.mp hk
        have hkk : k + 1 < nn := by omega
        have h1 : s (k + 1) ≠ 0 := (hs_pos (k + 1) (by omega)).ne'
        have hrec' := hrec (k + 1) (by omega) hkk
        rw [show k + 1 + 1 = k + 2 by omega, show k + 1 - 1 = k by omega] at hrec'
        have hkey : s (k + 2) = 2 * c * s (k + 1) - s k := by linarith
        rw [hkey]
        field_simp
        ring
      have hmid : (∑ k ∈ Finset.range (nn - 1), a (k + 1) ^ 2 * (s (k + 1 + 1) / s (k + 1)))
            + (∑ k ∈ Finset.range (nn - 1), a (k + 1) ^ 2 * (s k / s (k + 1)))
          = 2 * c * ∑ k ∈ Finset.range (nn - 1), a (k + 1) ^ 2 := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k hk => hmidpt k hk)
      have hG0 : a 0 ^ 2 * (s 1 / s 0) = 2 * c * a 0 ^ 2 := by
        have h1 : s 0 ≠ 0 := (hs_pos 0 (by omega)).ne'
        rw [hb0]
        field_simp
      have hHn : a nn ^ 2 * (s (nn - 1) / s nn) = 2 * c * a nn ^ 2 := by
        have h1 : s nn ≠ 0 := (hs_pos nn le_rfl).ne'
        rw [hbn]
        field_simp
      have hSsplit : (∑ k ∈ Finset.range (nn + 1), a k ^ 2)
          = a 0 ^ 2 + (∑ k ∈ Finset.range (nn - 1), a (k + 1) ^ 2) + a nn ^ 2 := by
        rw [Finset.sum_range_succ']
        conv_lhs => rw [show nn = (nn - 1) + 1 by omega]
        rw [Finset.sum_range_succ]
        rw [Nat.sub_add_cancel hnn]
        ring
      rw [hGsplit, hHsplit, ht2, hSsplit]
      linarith [hmid, hG0, hHn]
    constructor
    · have h := key_id s
      have hzero : ∀ k ∈ Finset.range nn,
          (s k * s (k + 1) - s (k + 1) * s k) ^ 2 / (s k * s (k + 1)) = 0 := by
        intro k hk
        rw [show s k * s (k + 1) - s (k + 1) * s k = 0 by ring]
        simp
      rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero] at h
      linarith
    · intro a
      have h := key_id a
      have hnn : 0 ≤ ∑ k ∈ Finset.range nn,
          (a k * s (k + 1) - a (k + 1) * s k) ^ 2 / (s k * s (k + 1)) := by
        apply Finset.sum_nonneg
        intro k hk
        have hk' : k < nn := Finset.mem_range.mp hk
        apply div_nonneg (sq_nonneg _)
        exact (mul_pos (hs_pos k (by omega)) (hs_pos (k + 1) (by omega))).le
      nlinarith [h, hnn]
  constructor
  · intro n
    by_cases hn0 : n = 0
    · subst hn0
      have hval : Real.sin (Real.pi / (2 * (((0 : ℕ) : ℝ) + 2))) ^ 2 = 1 / 2 := by
        have harg : (2 : ℝ) * (((0 : ℕ) : ℝ) + 2) = 4 := by norm_num
        rw [harg, Real.sin_pi_div_four, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      rw [hval]
      have hset : {v : ℝ | ∃ a : Fin (0 + 1) → ℝ, (∀ k, 0 ≤ a k) ∧ ∑ k, a k ^ 2 = 1 ∧
          v = (1 / 2 : ℝ) * (1 - ∑ k : Fin 0, a k.castSucc * a k.succ)} = {1 / 2} := by
        ext v
        constructor
        · rintro ⟨a, ha0, ha1, rfl⟩
          simp
        · intro hv
          rw [Set.mem_singleton_iff] at hv
          subst hv
          exact ⟨fun _ => 1, fun k => by norm_num, by simp, by simp⟩
      rw [hset]
      exact ⟨by simp, fun v hv => by rw [Set.mem_singleton_iff] at hv; rw [hv]⟩
    · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
      set θ : ℝ := Real.pi / ((n : ℝ) + 2) with hθdef
      have hn2pos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      have hθpos : 0 < θ := by rw [hθdef]; positivity
      have hθn : ((n : ℝ) + 2) * θ = Real.pi := by
        rw [hθdef]; field_simp
      let φ : ℕ → ℝ := fun k => Real.sin (((k : ℝ) + 1) * θ)
      let c : ℝ := Real.cos θ
      have hs_pos : ∀ k ≤ n, 0 < φ k := by
        intro k hk
        dsimp only [φ]
        apply Real.sin_pos_of_pos_of_lt_pi
        · have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
          nlinarith [hθpos]
        · have hk1 : (k : ℝ) + 1 ≤ (n : ℝ) + 1 := by
            have : k + 1 ≤ n + 1 := Nat.add_le_add_right hk 1
            exact_mod_cast this
          have hstep : ((k : ℝ) + 1) * θ ≤ ((n : ℝ) + 1) * θ :=
            mul_le_mul_of_nonneg_right hk1 hθpos.le
          have hlt : ((n : ℝ) + 1) * θ < Real.pi := by
            have h1 : ((n : ℝ) + 1) * θ = Real.pi * (((n : ℝ) + 1) / ((n : ℝ) + 2)) := by
              rw [hθdef]; field_simp
            rw [h1]
            have h2 : ((n : ℝ) + 1) / ((n : ℝ) + 2) < 1 := by
              rw [div_lt_one hn2pos]; linarith
            nlinarith [Real.pi_pos]
          linarith
      have hrec : ∀ k, 1 ≤ k → k < n → φ (k + 1) + φ (k - 1) = 2 * c * φ k := by
        intro k hk hkn
        have hc1 : ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 := by push_cast; ring
        have hc2 : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
          have h : k - 1 + 1 = k := Nat.sub_add_cancel hk
          exact_mod_cast h
        have e1 : ((k : ℝ) + 2) * θ = ((k : ℝ) + 1) * θ + θ := by ring
        have e2 : (k : ℝ) * θ = ((k : ℝ) + 1) * θ - θ := by ring
        simp only [φ, c]
        rw [hc1, hc2, e1, e2, Real.sin_add, Real.sin_sub]
        ring
      have hb0 : φ 1 = 2 * c * φ 0 := by
        simp only [φ, c]
        norm_num only [Nat.cast_one, Nat.cast_zero, zero_add]
        rw [Real.sin_two_mul]
        ring
      have hbn : φ (n - 1) = 2 * c * φ n := by
        have hc2 : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
          have h : n - 1 + 1 = n := Nat.sub_add_cancel hn1
          exact_mod_cast h
        have hnθ : (n : ℝ) * θ = Real.pi - 2 * θ := by nlinarith [hθn]
        have hn1θ : ((n : ℝ) + 1) * θ = Real.pi - θ := by nlinarith [hθn]
        simp only [φ, c, hc2]
        rw [hnθ, hn1θ, Real.sin_pi_sub, Real.sin_pi_sub, Real.sin_two_mul]
        ring
      have hinst := key_abstract n hn1 φ c hs_pos hrec hb0 hbn
      have hval_eq : (1 / 2 : ℝ) * (1 - c) = Real.sin (Real.pi / (2 * ((n : ℝ) + 2))) ^ 2 := by
        have hangle : Real.pi / (2 * ((n : ℝ) + 2)) = θ / 2 := by
          rw [hθdef]; field_simp
        rw [hangle]
        have hdouble : Real.cos (2 * (θ / 2)) = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
          rw [Real.cos_two_mul]
          have hsq := Real.sin_sq_add_cos_sq (θ / 2)
          nlinarith
        have hθ : 2 * (θ / 2) = θ := by ring
        rw [hθ] at hdouble
        simp only [c]
        linarith
      let D : ℝ := Real.sqrt (∑ k ∈ Finset.range (n + 1), φ k ^ 2)
      have hSpos : 0 < ∑ k ∈ Finset.range (n + 1), φ k ^ 2 := by
        have h0 : 0 < φ 0 ^ 2 := by
          have hh := hs_pos 0 (by omega)
          positivity
        exact Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨0, Finset.mem_range.mpr (by omega), h0⟩
      have hDpos : 0 < D := Real.sqrt_pos.mpr hSpos
      have hDsq : D ^ 2 = ∑ k ∈ Finset.range (n + 1), φ k ^ 2 := Real.sq_sqrt hSpos.le
      refine ⟨?_, ?_⟩
      · -- membership via the candidate
        have h1 : ∀ k : Fin (n + 1), 0 ≤ φ (k : ℕ) / D :=
          fun k => div_nonneg (hs_pos (k : ℕ) (by omega)).le hDpos.le
        have h2 : (∑ k : Fin (n + 1), (φ (k : ℕ) / D) ^ 2) = 1 := by
          rw [Fin.sum_univ_eq_sum_range (fun k => (φ k / D) ^ 2) (n + 1)]
          have hcalc : (∑ k ∈ Finset.range (n + 1), (φ k / D) ^ 2)
              = (∑ k ∈ Finset.range (n + 1), φ k ^ 2) / D ^ 2 := by
            rw [Finset.sum_div]
            exact Finset.sum_congr rfl (fun k _ => by rw [div_pow])
          rw [hcalc, hDsq]
          exact div_self hSpos.ne'
        have h3 : (∑ k : Fin n, (φ (k.castSucc : ℕ) / D) * (φ (k.succ : ℕ) / D)) = c := by
          have hstep : (∑ k : Fin n, (φ (k.castSucc : ℕ) / D) * (φ (k.succ : ℕ) / D))
              = ∑ k : Fin n, (φ (k : ℕ) / D) * (φ ((k : ℕ) + 1) / D) := by
            apply Finset.sum_congr rfl
            intro i _
            simp only [Fin.val_castSucc, Fin.val_succ]
          rw [hstep, Fin.sum_univ_eq_sum_range (fun k => (φ k / D) * (φ (k + 1) / D)) n]
          have hcalc : (∑ k ∈ Finset.range n, (φ k / D) * (φ (k + 1) / D))
              = (∑ k ∈ Finset.range n, φ k * φ (k + 1)) / D ^ 2 := by
            rw [Finset.sum_div]
            exact Finset.sum_congr rfl (fun k _ => by rw [div_mul_div_comm]; ring)
          rw [hcalc, hinst.1, hDsq]
          exact mul_div_cancel_right₀ c hSpos.ne'
        refine ⟨fun k => φ (k : ℕ) / D, h1, h2, ?_⟩
        rw [h3]
        exact hval_eq.symm
      · -- minimality
        rintro v ⟨a, ha0, ha1, rfl⟩
        rw [← hval_eq]
        have hb : (∑ k : Fin n, a k.castSucc * a k.succ)
            ≤ c * (∑ k : Fin (n + 1), a k ^ 2) := by
          let b : ℕ → ℝ := fun k => if h : k < n + 1 then a ⟨k, h⟩ else 0
          have hbS : ∑ k : Fin (n + 1), a k ^ 2 = ∑ k ∈ Finset.range (n + 1), b k ^ 2 := by
            rw [← Fin.sum_univ_eq_sum_range (fun k => b k ^ 2) (n + 1)]
            apply Finset.sum_congr rfl
            intro i _
            have hbi : b ↑i = a i := by
              simp only [b, dif_pos i.isLt]
            rw [hbi]
          have hbC : ∑ k : Fin n, a k.castSucc * a k.succ
              = ∑ k ∈ Finset.range n, b k * b (k + 1) := by
            rw [← Fin.sum_univ_eq_sum_range (fun k => b k * b (k + 1)) n]
            apply Finset.sum_congr rfl
            intro i _
            have h1 : b ↑i = a i.castSucc := by
              have hlt : (↑i : ℕ) < n + 1 := by omega
              dsimp only [b]
              rw [dif_pos hlt]
              congr 1
            have h2 : b (↑i + 1) = a i.succ := by
              have hlt : (↑i : ℕ) + 1 < n + 1 := by have := i.isLt; omega
              dsimp only [b]
              rw [dif_pos hlt]
              congr 1
            rw [h1, h2]
          rw [hbC, hbS]
          exact hinst.2 b
        rw [ha1] at hb
        nlinarith [hb]
  · -- limit
    have hshift : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
      have h2 : (1 : ℝ) + 1 = 2 := by norm_num
      simpa [Function.comp_def, one_div, Nat.cast_add, Nat.cast_one, add_assoc, h2] using h1
    have hx : Tendsto (fun n : ℕ => Real.pi / (2 * ((n : ℝ) + 2))) atTop (𝓝 0) := by
      have h2 : Tendsto (fun n : ℕ => (Real.pi / 2) * ((1 : ℝ) / ((n : ℝ) + 2))) atTop
          (𝓝 ((Real.pi / 2) * 0)) := Tendsto.const_mul (Real.pi / 2) hshift
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h2
    have hu : Tendsto (fun n : ℕ => ((n : ℝ) / ((n : ℝ) + 2)) ^ 2) atTop (𝓝 1) := by
      have heq : (fun n : ℕ => ((n : ℝ) / ((n : ℝ) + 2)) ^ 2)
          = (fun n : ℕ => (1 - 2 * ((1 : ℝ) / ((n : ℝ) + 2))) ^ 2) := by
        funext n
        field_simp
        ring
      rw [heq]
      have h1 : Tendsto (fun n : ℕ => 1 - 2 * ((1 : ℝ) / ((n : ℝ) + 2))) atTop (𝓝 (1 - 2 * 0)) :=
        tendsto_const_nhds.sub (Tendsto.const_mul 2 hshift)
      have h2 := h1.pow 2
      simpa using h2
    have hsinc : Tendsto (fun n : ℕ => (Real.sinc (Real.pi / (2 * ((n : ℝ) + 2)))) ^ 2) atTop (𝓝 1) := by
      have h1 : Tendsto (fun n : ℕ => Real.sinc (Real.pi / (2 * ((n : ℝ) + 2)))) atTop (𝓝 1) := by
        have := (Real.continuous_sinc.tendsto 0).comp hx
        simpa [Real.sinc_zero, Function.comp_def] using this
      simpa using h1.pow 2
    have hlim : Tendsto (fun n : ℕ => (Real.pi ^ 2 / 4) *
        (((n : ℝ) / ((n : ℝ) + 2)) ^ 2 * (Real.sinc (Real.pi / (2 * ((n : ℝ) + 2)))) ^ 2))
        atTop (𝓝 ((Real.pi ^ 2 / 4) * (1 * 1))) :=
      tendsto_const_nhds.mul (hu.mul hsinc)
    have hpt : ∀ n : ℕ, (n : ℝ) ^ 2 * Real.sin (Real.pi / (2 * ((n : ℝ) + 2))) ^ 2
        = (Real.pi ^ 2 / 4) *
          (((n : ℝ) / ((n : ℝ) + 2)) ^ 2 * (Real.sinc (Real.pi / (2 * ((n : ℝ) + 2)))) ^ 2) := by
      intro n
      have hxne : Real.pi / (2 * ((n : ℝ) + 2)) ≠ 0 := by positivity
      have hn2ne : ((n : ℝ) + 2) ≠ 0 := by positivity
      rw [Real.sinc_of_ne_zero hxne]
      field_simp
      ring
    have hfin : Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * Real.sin (Real.pi / (2 * ((n : ℝ) + 2))) ^ 2)
        atTop (𝓝 (Real.pi ^ 2 / 4)) := by
      have h1 : Tendsto (fun n : ℕ => (Real.pi ^ 2 / 4) *
          (((n : ℝ) / ((n : ℝ) + 2)) ^ 2 * (Real.sinc (Real.pi / (2 * ((n : ℝ) + 2)))) ^ 2))
          atTop (𝓝 (Real.pi ^ 2 / 4)) := by
        simpa using hlim
      exact h1.congr' (Filter.Eventually.of_forall (fun n => (hpt n).symm))
    exact hfin
