-- Prove2me | solution 1 for TeleDriving.AsymLimited.theorem_2A
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T08:18:28.424564+00:00
-- url     : https://prove2.me/submissions/550a7c7f-3ee0-4ac7-9660-f31755ab5371

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model
import Theorems.Thm_TeleDriving_AsymLimited_appD1_rho_gt

open TeleDriving.ScarceFleet

namespace Tele2AHelp

lemma w_succ (mu : ℕ → ℝ → ℝ) (lam : ℝ) (m i : ℕ) :
    weight mu lam m (i + 1) = weight mu lam m i * rho mu lam m ((i + 1 : ℕ) : ℝ) := by
  unfold weight
  rw [Finset.prod_Icc_succ_top (by omega)]

lemma w_split (mu : ℕ → ℝ → ℝ) (lam : ℝ) (m q n : ℕ) (hqn : q ≤ n) :
    weight mu lam m n = weight mu lam m q * ∏ k ∈ Finset.Ioc q n, rho mu lam m (k : ℝ) := by
  induction n, hqn using Nat.le_induction with
  | base => simp
  | succ n hqn ih =>
    rw [w_succ, ih, Finset.prod_Ioc_succ_top hqn, mul_assoc]

lemma Z_eq (mu : ℕ → ℝ → ℝ) (lam : ℝ) (m n : ℕ) :
    1 + ∑ i ∈ Finset.Icc 1 n, weight mu lam m i = ∑ i ∈ Finset.range (n + 1), weight mu lam m i := by
  induction n with
  | zero => simp [weight]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ← ih]; ring

lemma rho_pos (s lam : ℝ) (hs : 0 < s) (hlam : 0 < lam) (m : ℕ) (k : ℝ) (hk : 0 < k) :
    0 < rho (muBesbes s) lam m k := by
  unfold rho muBesbes
  have : 0 < s / Real.sqrt ((m : ℝ) - k + 1) + s := by positivity
  positivity

lemma w_pos (s lam : ℝ) (hs : 0 < s) (hlam : 0 < lam) (m i : ℕ) :
    0 < weight (muBesbes s) lam m i := by
  unfold weight
  apply Finset.prod_pos
  intro k hk
  simp at hk
  exact rho_pos s lam hs hlam m k (by exact_mod_cast (by omega : 0 < k))

lemma rho_eq (s lam : ℝ) (hs : 0 < s) (m : ℕ) (k : ℝ) (hk : 0 < k) :
    rho (muBesbes s) lam m k = lam * s * (1 / Real.sqrt ((m : ℝ) - k + 1) + 1) / k := by
  unfold rho muBesbes
  have : 0 < s / Real.sqrt ((m : ℝ) - k + 1) + s := by positivity
  field_simp


lemma prod_ge (f : ℕ → ℝ) (q n : ℕ) (r : ℝ) (hr : 0 ≤ r) (h : ∀ k ∈ Finset.Ioc q n, r ≤ f k) :
    r ^ (n - q) ≤ ∏ k ∈ Finset.Ioc q n, f k := by
  have := Finset.prod_le_prod (s := Finset.Ioc q n) (f := fun _ => r) (g := f)
    (fun _ _ => hr) h
  simpa [Finset.prod_const, Nat.card_Ioc] using this

lemma prod_le (f : ℕ → ℝ) (q n : ℕ) (R : ℝ) (h : ∀ k ∈ Finset.Ioc q n, 0 ≤ f k ∧ f k ≤ R) :
    ∏ k ∈ Finset.Ioc q n, f k ≤ R ^ (n - q) := by
  have := Finset.prod_le_prod (s := Finset.Ioc q n) (f := f) (g := fun _ => R)
    (fun k hk => (h k hk).1) (fun k hk => (h k hk).2)
  simpa [Finset.prod_const, Nat.card_Ioc] using this

lemma piMN_eq (mu : ℕ → ℝ → ℝ) (lam : ℝ) (m n : ℕ) :
    piMN mu lam m n n = weight mu lam m n / ∑ i ∈ Finset.range (n + 1), weight mu lam m i := by
  unfold piMN; rw [Z_eq]

/-- Upper bound on SL(m_λ, m_λ). -/
lemma SL_mm_le (s alpha lam : ℝ) (hs : 0 < s) (ha0 : 0 < alpha) (ha1 : alpha < 1) (hlam : 0 < lam)
    (hm : 1 ≤ mLam alpha s lam) :
    0 < SL (muBesbes s) lam (mLam alpha s lam) (mLam alpha s lam) ∧
    SL (muBesbes s) lam (mLam alpha s lam) (mLam alpha s lam) ≤ alpha / (2 - alpha) := by
  set m := mLam alpha s lam with hmdef
  set w := weight (muBesbes s) lam m with hw
  have wpos : ∀ i, 0 < w i := fun i => w_pos s lam hs hlam m i
  have hmle : (m : ℝ) ≤ alpha * lam * s := Nat.floor_le (by positivity)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  -- rho > 1/alpha on [1, m]
  have hrho := TeleDriving.AsymLimited.appD1_rho_gt s alpha hs ha0 ha1 lam hlam
  -- w i ≤ alpha^(m-1-i) w (m-1)
  have hwi : ∀ i ∈ Finset.range m, w i ≤ alpha ^ (m - 1 - i) * w (m - 1) := by
    intro i hi
    simp at hi
    have hsplit := w_split (muBesbes s) lam m i (m - 1) (by omega)
    have hp := prod_ge (fun k => rho (muBesbes s) lam m (k : ℝ)) i (m - 1) (1 / alpha) (by positivity)
      (by
        intro k hk
        simp at hk
        exact (hrho k (by simp; omega)).le)
    rw [← hw] at hsplit
    have h1 : w i * (1 / alpha) ^ (m - 1 - i) ≤ w (m - 1) := by
      rw [hsplit]; exact mul_le_mul_of_nonneg_left hp (wpos i).le
    have h2 : alpha ^ (m - 1 - i) * (1 / alpha) ^ (m - 1 - i) = 1 := by
      rw [← mul_pow]; field_simp; simp
    have h3 : 0 < alpha ^ (m - 1 - i) := by positivity
    calc w i = alpha ^ (m - 1 - i) * (w i * (1 / alpha) ^ (m - 1 - i)) := by
          rw [mul_comm (w i), ← mul_assoc, h2, one_mul]
      _ ≤ alpha ^ (m - 1 - i) * w (m - 1) := mul_le_mul_of_nonneg_left h1 h3.le
  -- w (m-1) ≤ alpha/2 * w m
  have hwm : w (m - 1) ≤ alpha / 2 * w m := by
    have hsucc := w_succ (muBesbes s) lam m (m - 1)
    rw [← hw, show m - 1 + 1 = m by omega] at hsucc
    have hr := rho_eq s lam hs m (m : ℝ) hmpos
    rw [show ((m : ℕ) : ℝ) - (m : ℝ) + 1 = 1 by ring, Real.sqrt_one] at hr
    rw [hsucc, hr]
    have := wpos (m - 1)
    have e : alpha / 2 * (w (m - 1) * (lam * s * (1 / 1 + 1) / m)) = w (m - 1) * (alpha * lam * s / m) := by
      field_simp; ring
    rw [e]
    have : 1 ≤ alpha * lam * s / m := by rw [le_div_iff₀ hmpos]; linarith
    nlinarith
  -- geometric sum
  have hgeom : ∑ i ∈ Finset.range m, alpha ^ (m - 1 - i) ≤ 1 / (1 - alpha) := by
    rw [Finset.sum_range_reflect (fun j => alpha ^ j) m]
    have := geom_sum_mul_neg alpha m
    rw [le_div_iff₀ (by linarith)]
    have : 0 < alpha ^ m := by positivity
    linarith
  have hsumle : ∑ i ∈ Finset.range m, w i ≤ w (m - 1) / (1 - alpha) := by
    calc ∑ i ∈ Finset.range m, w i ≤ ∑ i ∈ Finset.range m, alpha ^ (m - 1 - i) * w (m - 1) :=
          Finset.sum_le_sum hwi
      _ = (∑ i ∈ Finset.range m, alpha ^ (m - 1 - i)) * w (m - 1) := by rw [Finset.sum_mul]
      _ ≤ 1 / (1 - alpha) * w (m - 1) :=
          mul_le_mul_of_nonneg_right hgeom (wpos _).le
      _ = w (m - 1) / (1 - alpha) := by ring
  have hZ : ∑ i ∈ Finset.range (m + 1), w i = ∑ i ∈ Finset.range m, w i + w m :=
    Finset.sum_range_succ _ _
  have hZ0 : w 0 ≤ ∑ i ∈ Finset.range m, w i :=
    Finset.single_le_sum (fun i _ => (wpos i).le) (by simp; omega)
  unfold SL
  rw [piMN_eq, ← hw, hZ]
  have hwm0 := wpos m
  have hw0 := wpos 0
  have hS0 : 0 < ∑ i ∈ Finset.range m, w i := by linarith
  constructor
  · rw [sub_pos, div_lt_one (by linarith)]; linarith
  · have h1a : 0 < 1 - alpha := by linarith
    have hS : (∑ i ∈ Finset.range m, w i) * (1 - alpha) ≤ w (m - 1) := by
      rw [le_div_iff₀ h1a] at hsumle; exact hsumle
    rw [sub_le_iff_le_add, div_add_div _ _ (by linarith) (by linarith), le_div_iff₀ (mul_pos (by linarith) (by linarith)),
      one_mul]
    nlinarith

/-- Lower bound on SL(m_λ, m_λ - D). -/
lemma SL_lower (s alpha lam : ℝ) (hs : 0 < s) (ha0 : 0 < alpha) (hlam : 0 < lam)
    (D t : ℕ) (hm : D + t + 1 ≤ mLam alpha s lam) :
    ((mLam alpha s lam - D - t : ℕ) : ℝ) / (lam * s * (1 / Real.sqrt ((D : ℝ) + 1) + 1))
        - alpha ^ (t + 1) ≤ SL (muBesbes s) lam (mLam alpha s lam) (mLam alpha s lam - D) := by
  set m := mLam alpha s lam with hmdef
  set w := weight (muBesbes s) lam m with hw
  set n := m - D with hn
  set c := 1 / Real.sqrt ((D : ℝ) + 1) + 1 with hc
  set h := ((m - D - t : ℕ) : ℝ) / (lam * s * c) with hh
  have wpos : ∀ i, 0 < w i := fun i => w_pos s lam hs hlam m i
  have hmle : (m : ℝ) ≤ alpha * lam * s := Nat.floor_le (by positivity)
  have hc1 : 1 ≤ c := by rw [hc]; have : 0 ≤ 1 / Real.sqrt ((D : ℝ) + 1) := by positivity
                         linarith
  have hL : 0 < lam * s := by positivity
  have hnum : (1 : ℝ) ≤ ((m - D - t : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m - D - t)
  have hnumle : ((m - D - t : ℕ) : ℝ) ≤ m := by exact_mod_cast (by omega : m - D - t ≤ m)
  have hpos : 0 < h := by rw [hh]; positivity
  have hle : h ≤ alpha := by
    rw [hh, div_le_iff₀ (by positivity)]
    nlinarith
  -- rho ≤ 1/h on the top window
  have hrho : ∀ k ∈ Finset.Ioc (n - t) n,
      0 ≤ rho (muBesbes s) lam m (k : ℝ) ∧ rho (muBesbes s) lam m (k : ℝ) ≤ 1 / h := by
    intro k hk
    simp at hk
    have hk1 : ((m - D - t : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : m - D - t ≤ k)
    have hk0 : (0 : ℝ) < k := by linarith
    refine ⟨(rho_pos s lam hs hlam m k hk0).le, ?_⟩
    rw [rho_eq s lam hs m k hk0, hh, one_div_div]
    have hkm : (D : ℝ) + 1 ≤ (m : ℝ) - k + 1 := by
      have : k + D ≤ m := by omega
      have : ((k + D : ℕ) : ℝ) ≤ m := by exact_mod_cast this
      push_cast at this; linarith
    have hsq : 1 / Real.sqrt ((m : ℝ) - k + 1) ≤ 1 / Real.sqrt ((D : ℝ) + 1) :=
      one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_le_sqrt hkm)
    apply div_le_div₀ (by positivity) _ (by linarith) hk1
    rw [hc]; apply mul_le_mul_of_nonneg_left _ hL.le; linarith
  have hwj : ∀ j ∈ Finset.range (t + 1), h ^ j * w n ≤ w (n - j) := by
    intro j hj
    simp at hj
    have hsplit := w_split (muBesbes s) lam m (n - j) n (by omega)
    rw [← hw] at hsplit
    have hp := prod_le (fun k => rho (muBesbes s) lam m (k : ℝ)) (n - j) n (1 / h)
      (by
        intro k hk
        apply hrho k
        simp at hk ⊢; omega)
    rw [show n - (n - j) = j by omega] at hp
    have : w n ≤ w (n - j) * (1 / h) ^ j := by
      rw [hsplit]; exact mul_le_mul_of_nonneg_left hp (wpos _).le
    have e : h ^ j * (1 / h) ^ j = 1 := by rw [← mul_pow]; field_simp; simp
    calc h ^ j * w n ≤ h ^ j * (w (n - j) * (1 / h) ^ j) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = w (n - j) := by rw [mul_comm (w _), ← mul_assoc, e, one_mul]
  have hZ : ∑ j ∈ Finset.range (t + 1), w (n - j) ≤ ∑ i ∈ Finset.range (n + 1), w i := by
    rw [← Finset.sum_range_reflect w (n + 1)]
    simp only [Nat.add_sub_cancel]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
      (fun i _ _ => (wpos _).le)
  set S := ∑ j ∈ Finset.range (t + 1), h ^ j with hS
  have hwS : w n * S ≤ ∑ i ∈ Finset.range (n + 1), w i := by
    calc w n * S = ∑ j ∈ Finset.range (t + 1), h ^ j * w n := by
          rw [hS, Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
      _ ≤ ∑ j ∈ Finset.range (t + 1), w (n - j) := Finset.sum_le_sum hwj
      _ ≤ _ := hZ
  have hgeom := geom_sum_mul_neg h (t + 1)
  rw [← hS] at hgeom
  have hS1 : 1 ≤ S := by
    have := Finset.single_le_sum (f := fun j => h ^ j) (fun j _ => (pow_pos hpos j).le)
      (Finset.mem_range.mpr (Nat.succ_pos t))
    simpa [hS] using this
  have hpow : h ^ (t + 1) ≤ alpha ^ (t + 1) := pow_le_pow_left₀ hpos.le hle _
  have hapos : 0 < alpha ^ (t + 1) := by positivity
  have hkey : 1 ≤ (1 - h + alpha ^ (t + 1)) * S := by nlinarith
  have hZpos : 0 < ∑ i ∈ Finset.range (n + 1), w i :=
    Finset.sum_pos (fun i _ => wpos i) ⟨0, by simp⟩
  have hwn := wpos n
  unfold SL
  rw [piMN_eq, ← hw]
  have hfac : 0 ≤ 1 - h + alpha ^ (t + 1) := by nlinarith
  have : w n / ∑ i ∈ Finset.range (n + 1), w i ≤ 1 - h + alpha ^ (t + 1) := by
    rw [div_le_iff₀ hZpos]
    nlinarith
  linarith

lemma SL_nonneg (s lam : ℝ) (hs : 0 < s) (hlam : 0 < lam) (m n : ℕ) :
    0 ≤ SL (muBesbes s) lam m n := by
  unfold SL
  rw [piMN_eq]
  have wpos : ∀ i, 0 < weight (muBesbes s) lam m i := fun i => w_pos s lam hs hlam m i
  have hZ : weight (muBesbes s) lam m n ≤ ∑ i ∈ Finset.range (n + 1), weight (muBesbes s) lam m i :=
    Finset.single_le_sum (fun i _ => (wpos i).le) (by simp)
  have hZpos : 0 < ∑ i ∈ Finset.range (n + 1), weight (muBesbes s) lam m i :=
    Finset.sum_pos (fun i _ => wpos i) ⟨0, by simp⟩
  rw [sub_nonneg, div_le_one hZpos]; exact hZ

lemma alg_id (a h : ℝ) (t : ℕ) (ha : a ≠ 0) :
    (h - a ^ (t + 1)) * ((2 - a) / a) = (2 - a) * (h / a - a ^ t) := by
  rw [pow_succ]; field_simp

lemma final_arith (a ε h e1 iK p S : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hp : 0 ≤ p) (hp6 : p < ε / 6)
    (he1 : 0 ≤ e1) (he1le : e1 ≤ ε / 6) (hiK : 0 ≤ iK) (hiK6 : iK < ε / 6)
    (hh : 1 - e1 - iK ≤ h / a) (hLB : h - p * a ≤ S) : 2 - a - ε ≤ S * ((2 - a) / a) := by
  have h2a : 0 < 2 - a := by linarith
  have e : (h - p * a) * ((2 - a) / a) = (2 - a) * (h / a - p) := by field_simp
  have hm : (h - p * a) * ((2 - a) / a) ≤ S * ((2 - a) / a) :=
    mul_le_mul_of_nonneg_right hLB (by positivity)
  have hY : 1 - (e1 + iK + p) ≤ h / a - p := by linarith
  have h1 := mul_le_mul_of_nonneg_left hY h2a.le
  have h2 : (2 - a) * (e1 + iK + p) ≤ 2 * (e1 + iK + p) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h3 : (2 - a) * (1 - (e1 + iK + p)) = (2 - a) - (2 - a) * (e1 + iK + p) := by ring
  linarith

end Tele2AHelp

open Tele2AHelp in
theorem solution (s alpha : ℝ) (hs : 0 < s) (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ lam in Filter.atTop,
      2 - alpha - ε ≤ TeleDriving.ScarceFleet.maxSLRatio (TeleDriving.ScarceFleet.muBesbes s) lam (TeleDriving.ScarceFleet.mLam alpha s lam) := by
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt (6 / ε)
  have hKpos : (0 : ℝ) < K := lt_trans (by positivity) hK
  have hKe : 1 / (K : ℝ) < ε / 6 := by
    rw [div_lt_iff₀ hKpos]; rw [div_lt_iff₀ hε] at hK; linarith
  obtain ⟨t, ht⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 6 by positivity) ha1
  set D : ℕ := K ^ 2 with hD
  set T : ℝ := ((D : ℝ) + t + 2 + 6 * (1 + D + t) / ε) / (alpha * s) + 1 with hT
  filter_upwards [Filter.eventually_ge_atTop T] with lam hlamT
  have has : 0 < alpha * s := by positivity
  have hT0 : 0 < ((D : ℝ) + t + 2 + 6 * (1 + D + t) / ε) / (alpha * s) := by positivity
  have hlam : 0 < lam := by linarith
  set x := alpha * lam * s with hx
  have hxT : (D : ℝ) + t + 2 + 6 * (1 + D + t) / ε < x := by
    have h1 : ((D : ℝ) + t + 2 + 6 * (1 + D + t) / ε) / (alpha * s) < lam := by linarith
    rw [div_lt_iff₀ has] at h1; rw [hx]; linarith
  have hq : 0 ≤ 6 * (1 + (D : ℝ) + t) / ε := by positivity
  set m := mLam alpha s lam with hmdef
  have hmx : x < (m : ℝ) + 1 := Nat.lt_floor_add_one x
  have hmle : (m : ℝ) ≤ x := Nat.floor_le (by positivity)
  have hm : D + t + 1 ≤ m := by
    have : ((D + t + 1 : ℕ) : ℝ) < (m : ℝ) + 1 := by push_cast; linarith
    have : D + t + 1 < m + 1 := by exact_mod_cast this
    omega
  have hm1 : 1 ≤ m := by omega
  obtain ⟨hSLm0, hSLm⟩ := SL_mm_le s alpha lam hs ha0 ha1 hlam hm1
  have hLB := SL_lower s alpha lam hs ha0 hlam D t hm
  have hSLn0 := SL_nonneg s lam hs hlam m (m - D)
  -- the ratio at n = m - D is below the max
  have hratio : SL (muBesbes s) lam m (m - D) / SL (muBesbes s) lam m m ≤
      maxSLRatio (muBesbes s) lam m := by
    unfold maxSLRatio
    have := le_ciSup (Set.finite_range
      (fun n : Fin m => SL (muBesbes s) lam m ((n : ℕ) + 1) / SL (muBesbes s) lam m m)).bddAbove
      ⟨m - D - 1, by omega⟩
    simpa [show m - D - 1 + 1 = m - D by omega] using this
  have h2a : 0 < 2 - alpha := by linarith
  have hratio2 : SL (muBesbes s) lam m (m - D) * ((2 - alpha) / alpha) ≤
      SL (muBesbes s) lam m (m - D) / SL (muBesbes s) lam m m := by
    rw [le_div_iff₀ hSLm0]
    have : SL (muBesbes s) lam m m * ((2 - alpha) / alpha) ≤ 1 := by
      rw [le_div_iff₀ h2a] at hSLm
      rw [mul_div_assoc', div_le_one ha0]; linarith
    nlinarith
  -- arithmetic
  set c := 1 / Real.sqrt ((D : ℝ) + 1) + 1 with hc
  have hc1 : 1 ≤ c := by
    have : 0 ≤ 1 / Real.sqrt ((D : ℝ) + 1) := by positivity
    linarith
  have hcK : c ≤ 1 + 1 / K := by
    have : (K : ℝ) ≤ Real.sqrt ((D : ℝ) + 1) := by
      rw [show (K : ℝ) = Real.sqrt ((K : ℝ) ^ 2) from (Real.sqrt_sq hKpos.le).symm]
      apply Real.sqrt_le_sqrt; rw [hD]; push_cast; linarith
    have : 1 / Real.sqrt ((D : ℝ) + 1) ≤ 1 / K := one_div_le_one_div_of_le hKpos this
    linarith
  have hNcast : ((m - D - t : ℕ) : ℝ) = (m : ℝ) - D - t := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  rw [hNcast] at hLB
  set h := ((m : ℝ) - D - t) / (lam * s * c) with hh
  set e1 := (1 + (D : ℝ) + t) / x with he1
  have hxpos : 0 < x := by linarith
  have he1le : e1 ≤ ε / 6 := by
    rw [he1, div_le_iff₀ hxpos]
    have : 6 * (1 + (D : ℝ) + t) / ε * ε = 6 * (1 + D + t) := by field_simp
    nlinarith
  have he1nn : 0 ≤ e1 := by positivity
  set u := 1 - e1 with hu
  have hu1 : u ≤ 1 := by linarith
  have hu0 : 0 ≤ u := by
    rw [hu, he1, sub_nonneg, div_le_one hxpos]; linarith
  have hhα : u - 1 / K ≤ h / alpha := by
    have e : h / alpha = ((m : ℝ) - D - t) / x / c := by
      rw [hh, hx]; field_simp
    rw [e]
    have hN : x * u ≤ (m : ℝ) - D - t := by
      rw [hu, he1, mul_sub, mul_div_cancel₀ _ hxpos.ne']; linarith
    have h1 : u ≤ ((m : ℝ) - D - t) / x := by rw [le_div_iff₀ hxpos]; linarith
    have h2 : u / c ≤ ((m : ℝ) - D - t) / x / c := div_le_div_of_nonneg_right h1 (by linarith)
    have h3 : u - 1 / K ≤ u / c := by
      rw [le_div_iff₀ (by linarith)]
      have hk0 : 0 ≤ 1 / (K : ℝ) := by positivity
      nlinarith
    linarith
  have hK0 : 0 ≤ 1 / (K : ℝ) := by positivity
  have hat : 0 ≤ alpha ^ t := by positivity
  rw [pow_succ] at hLB
  have := final_arith alpha ε h e1 (1 / K) (alpha ^ t) (SL (muBesbes s) lam m (m - D)) ha0 ha1 hat ht
    he1nn he1le hK0 hKe hhα hLB
  exact this.trans (hratio2.trans hratio)
