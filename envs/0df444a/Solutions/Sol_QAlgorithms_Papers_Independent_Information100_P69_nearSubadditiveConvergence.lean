-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P69.nearSubadditiveConvergence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T05:47:36.207054+00:00
-- url     : https://prove2.me/submissions/1c8f6475-91b6-4337-8d21-8992cd67397d

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Information100.P69

attribute [local instance] Classical.propDecidable Classical.decEq

/-- dyadic doubling bound -/
theorem h54c_dyadic (a F : ℕ → ℝ)
    (hsub : ∀ n m, 1 ≤ n → 1 ≤ m → a (n+m) ≤ a n+a m+F (n+m))
    (m : ℕ) (hm : 1 ≤ m) (k : ℕ) :
    a (2^k*m) ≤ (2^k*m : ℝ) * (a m / m +
      ∑ j ∈ Finset.range k, F (2^(j+1)*m) / (2^(j+1)*m)) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  induction k with
  | zero => simp; field_simp; rfl
  | succ k ih =>
    have h1 : 1 ≤ 2^k*m := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have h2 := hsub (2^k*m) (2^k*m) h1 h1
    have he : 2^k*m + 2^k*m = 2^(k+1)*m := by ring
    rw [he] at h2
    rw [Finset.sum_range_succ]
    have hpos : (0:ℝ) < 2^(k+1)*m := by positivity
    push_cast
    have : (2^(k+1)*m : ℝ) * (a m / m + ∑ j ∈ Finset.range k, F (2^(j+1)*m) / (2^(j+1)*m) +
        F (2^(k+1)*m) / (2^(k+1)*m)) = 2 * ((2^k*m : ℝ) * (a m / m +
      ∑ j ∈ Finset.range k, F (2^(j+1)*m) / (2^(j+1)*m))) + F (2^(k+1)*m) := by
      field_simp; ring
    rw [← add_assoc, this]
    linarith

/-- binary decomposition bound -/
theorem h54c_binary (a F : ℕ → ℝ)
    (hsub : ∀ n m, 1 ≤ n → 1 ≤ m → a (n+m) ≤ a n+a m+F (n+m))
    (hF : ∀ n, 1 ≤ n → 0 ≤ F n)
    (hmono : ∀ n m, 1 ≤ n → n ≤ m → F n ≤ F m)
    (m : ℕ) (hm : 1 ≤ m) (β D : ℝ) (hβ : 0 ≤ β)
    (hdy : ∀ k, a (2^k*m) ≤ (2^k*m : ℝ) * β)
    (hD : ∀ r, 1 ≤ r → r < m → a r ≤ D) (hD0 : 0 ≤ D) :
    ∀ n, 1 ≤ n → a n ≤ β * n + D + (Real.logb 2 n + 1) * F n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hFn := hF n hn
    have hlog : 0 ≤ Real.logb 2 n := Real.logb_nonneg (by norm_num) (by exact_mod_cast hn)
    by_cases hnm : n < m
    · have := hD n hn hnm
      have : 0 ≤ β * n := by positivity
      nlinarith
    · push Not at hnm
      set q := n / m with hq
      have hq1 : 1 ≤ q := (Nat.one_le_div_iff (by omega)).mpr hnm
      set k := Nat.log 2 q
      have hk1 : 2^k ≤ q := Nat.pow_log_le_self 2 (by omega)
      have hk2 : q < 2^(k+1) := Nat.lt_pow_succ_log_self (by norm_num) q
      have hqm : q * m ≤ n := Nat.div_mul_le_self n m
      have hn2 : n < (q+1) * m := by
        have := Nat.lt_div_mul_add (a := n) (b := m) (by omega)
        rw [← hq] at this; linarith
      have hA : 2^k*m ≤ n := le_trans (Nat.mul_le_mul_right m hk1) hqm
      have hB : n < 2^(k+1)*m := lt_of_lt_of_le hn2 (Nat.mul_le_mul_right m hk2)
      set n' := n - 2^k*m with hn'
      have hdk := hdy k
      by_cases h0 : n' = 0
      · have hnn : n = 2^k*m := by omega
        have h0' : 0 ≤ (Real.logb 2 n + 1) * F n := mul_nonneg (by linarith) hFn
        have hdk2 : a n ≤ (n:ℝ) * β := by rw [hnn]; push_cast; exact hdk
        nlinarith
      · have hn'1 : 1 ≤ n' := by omega
        have h2n : 2 * n' ≤ n := by
          have : 2^(k+1)*m = 2 * (2^k*m) := by ring
          omega
        have hlt : n' < n := by omega
        have ih' := ih n' hlt hn'1
        have h1 : 1 ≤ 2^k*m := Nat.one_le_iff_ne_zero.mpr (by positivity)
        have hs := hsub (2^k*m) n' h1 hn'1
        have he : 2^k*m + n' = n := by omega
        rw [he] at hs
        have hFF := hmono n' n hn'1 hlt.le
        have hF' := hF n' hn'1
        have hlogs : Real.logb 2 n' + 1 ≤ Real.logb 2 n := by
          have : Real.logb 2 ((2:ℝ) * n') ≤ Real.logb 2 n :=
            Real.logb_le_logb_of_le (by norm_num) (by positivity) (by exact_mod_cast h2n)
          rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one (by norm_num)] at this
          linarith
        have hl' : 0 ≤ Real.logb 2 n' + 1 := by
          have := Real.logb_nonneg (b := 2) (x := n') (by norm_num) (by exact_mod_cast hn'1)
          linarith
        have hcast : (n:ℝ) = 2^k*m + n' := by exact_mod_cast he.symm
        push_cast at hdk
        have : (Real.logb 2 n' + 1) * F n' ≤ (Real.logb 2 n) * F n := by
          calc (Real.logb 2 n' + 1) * F n' ≤ (Real.logb 2 n' + 1) * F n :=
                mul_le_mul_of_nonneg_left hFF hl'
            _ ≤ Real.logb 2 n * F n := mul_le_mul_of_nonneg_right hlogs hFn
        rw [hcast] at *
        nlinarith

theorem h54c_Fbound (F : ℕ → ℝ)
    (hF : ∀ n, 1 ≤ n → 0 ≤ F n)
    (hmono : ∀ n m, 1 ≤ n → n ≤ m → F n ≤ F m)
    (hbound : ∃ K : ℝ, 0 < K ∧ ∃ n0 : ℕ, ∀ n, 1 ≤ n → n0 ≤ n →
      F n ≤ K*(n:ℝ)^(2/3:ℝ)*Real.logb 2 ((n:ℝ)+1)) :
    ∃ G H : ℝ, 0 ≤ G ∧ 0 ≤ H ∧ ∀ n, 1 ≤ n → F n ≤ G * (n:ℝ)^(3/4:ℝ) + H := by
  obtain ⟨K, hK, n0, hb⟩ := hbound
  refine ⟨48*K, F (max n0 1), by positivity, hF _ (le_max_right _ _), ?_⟩
  intro n hn
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hG : 0 ≤ 48*K*(n:ℝ)^(3/4:ℝ) := by positivity
  by_cases h : n0 ≤ n
  · have h1 := hb n hn h
    have hl2 : (1/2:ℝ) < Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have hlog : Real.log ((n:ℝ)+1) ≤ ((n:ℝ)+1)^(1/12:ℝ) / (1/12) :=
      Real.log_le_rpow_div (by positivity) (by norm_num)
    have hp : ((n:ℝ)+1)^(1/12:ℝ) ≤ (2*(n:ℝ))^(1/12:ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    have hp2 : (2*(n:ℝ))^(1/12:ℝ) = (2:ℝ)^(1/12:ℝ) * (n:ℝ)^(1/12:ℝ) :=
      Real.mul_rpow (by norm_num) (by positivity)
    have hp3 : (2:ℝ)^(1/12:ℝ) ≤ 2 := by
      calc (2:ℝ)^(1/12:ℝ) ≤ (2:ℝ)^(1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have hlogb : Real.logb 2 ((n:ℝ)+1) ≤ 48 * (n:ℝ)^(1/12:ℝ) := by
      rw [Real.logb]
      have hpos : 0 ≤ Real.log ((n:ℝ)+1) := Real.log_nonneg (by linarith)
      have hq : 0 ≤ (n:ℝ)^(1/12:ℝ) := by positivity
      rw [div_le_iff₀ (by linarith)]
      have : Real.log ((n:ℝ)+1) ≤ 24 * (n:ℝ)^(1/12:ℝ) := by
        rw [hp2] at hp
        have : ((n:ℝ)+1)^(1/12:ℝ) / (1/12) = 12 * ((n:ℝ)+1)^(1/12:ℝ) := by ring
        nlinarith
      nlinarith
    have hrp : (n:ℝ)^(2/3:ℝ) * (n:ℝ)^(1/12:ℝ) = (n:ℝ)^(3/4:ℝ) := by
      rw [← Real.rpow_add (by linarith)]; norm_num
    have hq : 0 ≤ (n:ℝ)^(2/3:ℝ) := by positivity
    have hH := hF (max n0 1) (le_max_right _ _)
    calc F n ≤ K*(n:ℝ)^(2/3:ℝ)*Real.logb 2 ((n:ℝ)+1) := h1
      _ ≤ K*(n:ℝ)^(2/3:ℝ)*(48 * (n:ℝ)^(1/12:ℝ)) :=
          mul_le_mul_of_nonneg_left hlogb (by positivity)
      _ = 48*K*((n:ℝ)^(2/3:ℝ) * (n:ℝ)^(1/12:ℝ)) := by ring
      _ = 48*K*(n:ℝ)^(3/4:ℝ) := by rw [hrp]
      _ ≤ 48*K*(n:ℝ)^(3/4:ℝ) + F (max n0 1) := by linarith
  · push Not at h
    have : F n ≤ F (max n0 1) := hmono n _ hn (by omega)
    linarith

theorem h54c_geom (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) (k : ℕ) :
    ∑ j ∈ Finset.range k, r^(j+1) ≤ 1/(1-r) := by
  have : ∑ j ∈ Finset.range k, r^(j+1) ≤ ∑ j ∈ Finset.range (k+1), r^j := by
    rw [Finset.sum_range_succ']; simp
  refine this.trans ?_
  rw [geom_sum_eq h1.ne]
  have e : (r^(k+1)-1)/(r-1) = (1-r^(k+1))/(1-r) := by
    rw [← neg_div_neg_eq]; ring_nf
  rw [e]
  have : 0 ≤ r^(k+1) := pow_nonneg h0 _
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

theorem h54c_esum (F : ℕ → ℝ) (G H : ℝ) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hFb : ∀ n, 1 ≤ n → F n ≤ G * (n:ℝ)^(3/4:ℝ) + H)
    (m : ℕ) (hm : 1 ≤ m) (k : ℕ) :
    ∑ j ∈ Finset.range k, F (2^(j+1)*m) / (2^(j+1)*m) ≤
      G / (m:ℝ)^(1/4:ℝ) * (1/(1-((2:ℝ)^(1/4:ℝ))⁻¹)) + H / m * 2 := by
  set t : ℝ := (2:ℝ)^(1/4:ℝ) with ht
  have ht1 : 1 < t := Real.one_lt_rpow (by norm_num) (by norm_num)
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hmq : 0 < (m:ℝ)^(1/4:ℝ) := by positivity
  have key : ∀ j : ℕ, F (2^(j+1)*m) / (2^(j+1)*m) ≤
      G / (m:ℝ)^(1/4:ℝ) * (t⁻¹)^(j+1) + H / m * (1/2)^(j+1) := by
    intro j
    have h1 : 1 ≤ 2^(j+1)*m := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hb := hFb _ h1
    push_cast at hb
    set x : ℝ := 2^(j+1)*m with hx
    have hxpos : 0 < x := by positivity
    have hx34 : x^(3/4:ℝ) = x / x^(1/4:ℝ) := by
      rw [eq_div_iff (by positivity), ← Real.rpow_add hxpos]; norm_num
    have hx14 : x^(1/4:ℝ) = t^(j+1) * (m:ℝ)^(1/4:ℝ) := by
      rw [hx, Real.mul_rpow (by positivity) (by positivity), ht, ← Real.rpow_natCast,
        ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num)]
      ring_nf
    calc F (2^(j+1)*m) / x ≤ (G * x^(3/4:ℝ) + H) / x := div_le_div_of_nonneg_right hb hxpos.le
      _ = G / x^(1/4:ℝ) + H / x := by rw [hx34]; field_simp
      _ = G / (m:ℝ)^(1/4:ℝ) * (t⁻¹)^(j+1) + H / m * (1/2)^(j+1) := by
          rw [hx14, hx, inv_pow, one_div_pow]; field_simp
  calc ∑ j ∈ Finset.range k, F (2^(j+1)*m) / (2^(j+1)*m)
      ≤ ∑ j ∈ Finset.range k, (G / (m:ℝ)^(1/4:ℝ) * (t⁻¹)^(j+1) + H / m * (1/2)^(j+1)) :=
        Finset.sum_le_sum (fun j _ => key j)
    _ = G / (m:ℝ)^(1/4:ℝ) * ∑ j ∈ Finset.range k, (t⁻¹)^(j+1) +
        H / m * ∑ j ∈ Finset.range k, (1/2:ℝ)^(j+1) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ G / (m:ℝ)^(1/4:ℝ) * (1/(1-t⁻¹)) + H / m * (1/(1-1/2)) := by
        gcongr
        · exact h54c_geom _ (by positivity) (inv_lt_one_of_one_lt₀ ht1) k
        · exact h54c_geom _ (by norm_num) (by norm_num) k
    _ = _ := by norm_num

theorem h54c_logfac (n : ℕ) (hn : 1 ≤ n) :
    Real.logb 2 n + 1 ≤ 17 * (n:ℝ)^(1/8:ℝ) := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hl2 : (1/2:ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hlog : Real.log n ≤ (n:ℝ)^(1/8:ℝ) / (1/8) :=
    Real.log_le_rpow_div (by positivity) (by norm_num)
  have h1 : 1 ≤ (n:ℝ)^(1/8:ℝ) := Real.one_le_rpow hn' (by norm_num)
  have hpos : 0 ≤ Real.log n := Real.log_nonneg hn'
  have : Real.logb 2 n ≤ 16 * (n:ℝ)^(1/8:ℝ) := by
    rw [Real.logb, div_le_iff₀ (by linarith)]
    have : (n:ℝ)^(1/8:ℝ) / (1/8) = 8 * (n:ℝ)^(1/8:ℝ) := by ring
    nlinarith
  linarith

/-- the error term tends to zero -/
theorem h54c_err (G H D : ℝ) (hG : 0 ≤ G) (hH : 0 ≤ H) (hD : 0 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, D / n + (17 * (n:ℝ)^(1/8:ℝ)) * (G * (n:ℝ)^(3/4:ℝ) + H) / n ≤ ε := by
  have hlim : Tendsto (fun n : ℕ => D / n + 17 * (G+H) / (n:ℝ)^(1/8:ℝ)) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => D / (n:ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => 17 * (G+H) / (n:ℝ)^(1/8:ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop
        ((tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop)
    simpa using h1.add h2
  have hev := (hlim.eventually (gt_mem_nhds hε))
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn1
  have hnpos : (0:ℝ) < n := by linarith
  set y := (n:ℝ)^(1/8:ℝ) with hy
  have hy1 : 1 ≤ y := Real.one_le_rpow hn' (by norm_num)
  have hy8 : (n:ℝ) = y^8 := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]; norm_num
  have hy6 : (n:ℝ)^(3/4:ℝ) = y^6 := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]; norm_num
  have : (17 * y) * (G * y^6 + H) / y^8 ≤ 17 * (G+H) / y := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 1 ≤ y^6 := one_le_pow₀ hy1
    have hy0 : 0 ≤ y := by linarith
    have e1 : (17 * y) * (G * y^6 + H) * y = 17 * y^2 * (G*y^6 + H) := by ring
    have e2 : 17 * (G+H) * y^8 = 17 * y^2 * (G*y^6 + H*y^6) := by ring
    rw [e1, e2]
    have : H ≤ H * y^6 := by nlinarith
    have : 0 ≤ 17 * y^2 := by positivity
    nlinarith
  rw [hy6]
  rw [hy8] at hn ⊢
  calc D / y^8 + (17 * y) * (G * y^6 + H) / y^8 ≤ D / y^8 + 17 * (G+H) / y := by linarith
    _ ≤ ε := by
      rw [← hy8] at hn ⊢
      linarith

theorem h54c_upper (a F : ℕ → ℝ) (C0 C1 : ℝ)
    (ha : ∀ n, 1 ≤ n → 0 ≤ a n ∧ a n ≤ C0*n+C1)
    (hsub : ∀ n m, 1 ≤ n → 1 ≤ m → a (n+m) ≤ a n+a m+F (n+m))
    (hF : ∀ n, 1 ≤ n → 0 ≤ F n)
    (hmono : ∀ n m, 1 ≤ n → n ≤ m → F n ≤ F m)
    (G H : ℝ) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hFb : ∀ n, 1 ≤ n → F n ≤ G * (n:ℝ)^(3/4:ℝ) + H)
    (m : ℕ) (hm : 1 ≤ m) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, a n / n ≤ a m / m +
      (G / (m:ℝ)^(1/4:ℝ) * (1/(1-((2:ℝ)^(1/4:ℝ))⁻¹)) + H / m * 2) + ε := by
  have ht1 : 1 < (2:ℝ)^(1/4:ℝ) := Real.one_lt_rpow (by norm_num) (by norm_num)
  have hc : 0 < 1/(1-((2:ℝ)^(1/4:ℝ))⁻¹) := by
    have := inv_lt_one_of_one_lt₀ ht1
    apply div_pos one_pos; linarith
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  set e := G / (m:ℝ)^(1/4:ℝ) * (1/(1-((2:ℝ)^(1/4:ℝ))⁻¹)) + H / m * 2 with he
  have he0 : 0 ≤ e := by positivity
  set β := a m / m + e with hβ
  have hβ0 : 0 ≤ β := by have := (ha m hm).1; positivity
  have hdy : ∀ k, a (2^k*m) ≤ (2^k*m : ℝ) * β := by
    intro k
    have h1 := h54c_dyadic a F hsub m hm k
    have h2 := h54c_esum F G H hG hH hFb m hm k
    refine h1.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  set D := |C0| * m + |C1| with hD
  have hD0 : 0 ≤ D := by positivity
  have hDr : ∀ r, 1 ≤ r → r < m → a r ≤ D := by
    intro r hr hrm
    have h := (ha r hr).2
    have : (r:ℝ) ≤ m := by exact_mod_cast hrm.le
    have : C0 * r ≤ |C0| * m := by
      calc C0 * r ≤ |C0| * r := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ ≤ |C0| * m := mul_le_mul_of_nonneg_left this (abs_nonneg _)
    have := le_abs_self C1
    linarith
  have hbin := h54c_binary a F hsub hF hmono m hm β D hβ0 hdy hDr hD0
  filter_upwards [h54c_err G H D hG hH hD0 ε hε, eventually_ge_atTop 1] with n hn hn1
  have hb := hbin n hn1
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
  have hl := h54c_logfac n hn1
  have hl0 : 0 ≤ Real.logb 2 n + 1 := by
    have := Real.logb_nonneg (b := 2) (x := n) (by norm_num) (by exact_mod_cast hn1); linarith
  have hFn := hF n hn1
  have hFb' := hFb n hn1
  have : (Real.logb 2 n + 1) * F n ≤ (17 * (n:ℝ)^(1/8:ℝ)) * (G * (n:ℝ)^(3/4:ℝ) + H) :=
    mul_le_mul hl hFb' hFn (by linarith)
  rw [div_le_iff₀ hnpos]
  have e2 : (β + D / n + (17 * (n:ℝ)^(1/8:ℝ)) * (G * (n:ℝ)^(3/4:ℝ) + H) / n) * n =
      β * n + D + (17 * (n:ℝ)^(1/8:ℝ)) * (G * (n:ℝ)^(3/4:ℝ) + H) := by
    field_simp
  have : a n ≤ (β + D / n + (17 * (n:ℝ)^(1/8:ℝ)) * (G * (n:ℝ)^(3/4:ℝ) + H) / n) * n := by
    rw [e2]; linarith
  calc a n ≤ _ := this
    _ ≤ (β + ε) * n := by
        apply mul_le_mul_of_nonneg_right _ hnpos.le
        linarith

end QAlgorithms.Papers.Independent.Information100.P69

open QAlgorithms.Papers.Independent.Information100.P69

/-- Lemma 34, finite ordinary convergence for the specified summably controlled remainder;
no channel hypotheses; arXiv:2609.30762v1, PDF p.41. -/
theorem solution (a F : ℕ → ℝ) (C0 C1 : ℝ)
    (ha : ∀ n, 1 ≤ n → 0 ≤ a n ∧ a n ≤ C0*n+C1)
    (hsub : ∀ n m, 1 ≤ n → 1 ≤ m → a (n+m) ≤ a n+a m+F (n+m))
    (hF : ∀ n, 1 ≤ n → 0 ≤ F n)
    (hmono : ∀ n m, 1 ≤ n → n ≤ m → F n ≤ F m)
    (hbound : ∃ K : ℝ, 0 < K ∧ ∃ n0 : ℕ, ∀ n, 1 ≤ n → n0 ≤ n →
      F n ≤ K*(n:ℝ)^(2/3:ℝ)*Real.logb 2 ((n:ℝ)+1)) :
    ∃ R : ℝ, Tendsto (fun j : ℕ => a (j+1)/(j+1)) atTop (nhds R) := by
  obtain ⟨G, H, hG, hH, hFb⟩ := h54c_Fbound F hF hmono hbound
  set u : ℕ → ℝ := fun j : ℕ => a (j+1)/(j+1) with hu
  have hu0 : ∀ j, 0 ≤ u j := fun j => by
    have := (ha (j+1) (by omega)).1; simp only [hu]; positivity
  have hu1 : ∀ j, u j ≤ |C0| + |C1| := fun j => by
    have h := (ha (j+1) (by omega)).2
    simp only [hu]
    have hp : (0:ℝ) < (j:ℝ)+1 := by positivity
    rw [div_le_iff₀ hp]
    push_cast at h
    have : C0 * ((j:ℝ)+1) ≤ |C0| * ((j:ℝ)+1) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hp.le
    have : |C1| ≤ |C1| * ((j:ℝ)+1) := by
      have : (1:ℝ) ≤ (j:ℝ)+1 := by linarith [(j.cast_nonneg : (0:ℝ) ≤ j)]
      nlinarith [abs_nonneg C1]
    have := le_abs_self C1
    nlinarith
  have hbl : IsBoundedUnder (· ≥ ·) atTop u := isBoundedUnder_of ⟨0, hu0⟩
  have hbu : IsBoundedUnder (· ≤ ·) atTop u := isBoundedUnder_of ⟨_, hu1⟩
  set c := 1/(1-((2:ℝ)^(1/4:ℝ))⁻¹)
  have helim : Tendsto (fun m : ℕ => G / (m:ℝ)^(1/4:ℝ) * c + H / m * 2) atTop (nhds 0) := by
    have h1 : Tendsto (fun m : ℕ => H / (m:ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun m : ℕ => G / (m:ℝ)^(1/4:ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop
        ((tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop)
    simpa using (h2.mul_const c).add (h1.mul_const 2)
  refine ⟨liminf u atTop, tendsto_order.2 ⟨fun b hb => eventually_lt_of_lt_liminf hb hbl, ?_⟩⟩
  intro b hb
  set s := liminf u atTop
  set ε := (b - s)/3 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hfr : ∃ᶠ j in atTop, u j < s + ε :=
    frequently_lt_of_liminf_lt hbu.isCoboundedUnder_ge (by linarith)
  have hev : ∀ᶠ j : ℕ in atTop, G / ((j+1:ℕ):ℝ)^(1/4:ℝ) * c + H / ((j+1:ℕ):ℝ) * 2 < ε :=
    (tendsto_add_atTop_nat 1).eventually (helim.eventually (gt_mem_nhds hε0))
  obtain ⟨j, hj1, hj2⟩ := (hfr.and_eventually hev).exists
  have hup := h54c_upper a F C0 C1 ha hsub hF hmono G H hG hH hFb (j+1) (by omega) ε hε0
  have hup' := (tendsto_add_atTop_nat 1).eventually hup
  filter_upwards [hup'] with n hn
  have huj : u j = a (j+1) / ((j+1:ℕ):ℝ) := by simp only [hu]; push_cast; rfl
  have hun : u n = a (n+1) / ((n+1:ℕ):ℝ) := by simp only [hu]; push_cast; rfl
  rw [hun]
  rw [huj] at hj1
  linarith


end
