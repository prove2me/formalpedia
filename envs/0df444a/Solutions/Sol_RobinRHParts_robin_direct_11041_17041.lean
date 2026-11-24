-- Prove2me | solution 1 for RobinRHParts.robin_direct_11041_17041
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-24T03:17:15.482655+00:00
-- url     : https://prove2.me/submissions/e5e8059e-e236-4e88-abac-4102a21b5984

import Mathlib

-- ===== Fix =====

/-! Fixed-point (scale `2^64`) natural-number arithmetic with real soundness lemmas. -/

set_option autoImplicit false
open Finset

namespace RobinFix

def D : ℕ := 2^64
def QL : ℕ := 4096
def cdiv (a b : ℕ) : ℕ := (a + b - 1) / b
def fdivL (a b : ℕ) : ℕ := a * D / b
def fdivU (a b : ℕ) : ℕ := cdiv (a * D) b
def L2lo : ℕ := fdivL 6931471803 (10^10)
def L2hi : ℕ := fdivU 6931471808 (10^10)
def bgo : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, lo, _ => lo
  | f+1, N, lo, hi => if hi ≤ lo + 1 then lo else
      if Nat.ble (Nat.pow 2 ((lo+hi)/2)) N then bgo f N ((lo+hi)/2) hi else bgo f N lo ((lo+hi)/2)
/-- binary-search base-2 logarithm (only used through checked guards) -/
def blog2 (N : ℕ) : ℕ := bgo 22 N 0 (Nat.pow 2 22)
def powN (Q r s : ℕ) : ℕ := Nat.pow r Q / Nat.pow s Q
def logLo (Q r s : ℕ) : ℕ :=
  if Nat.pow 2 (blog2 (powN Q r s)) ≤ powN Q r s then blog2 (powN Q r s) * L2lo / Q else 0
def logHi (Q r s : ℕ) : ℕ :=
  if powN Q r s < Nat.pow 2 (blog2 (powN Q r s) + 1) then
    cdiv ((blog2 (powN Q r s) + 1) * L2hi) Q else r * D
def fmulL (x y : ℕ) : ℕ := x * y / D
def fmulU (x y : ℕ) : ℕ := cdiv (x * y) D
/-- lower bound for `-log(1-u/v)` (scaled) -/
def mlogLo (u v n : ℕ) : ℕ := ∑ i ∈ range n, fdivL (u^(i+1)) (v^(i+1) * (i+1))
/-- upper bound for `-log(1-u/v)` (scaled) -/
def mlogHi (u v n : ℕ) : ℕ :=
  ∑ i ∈ range n, fdivU (u^(i+1)) (v^(i+1) * (i+1)) + fdivU (u^(n+1)) (v^n * (v - u))

noncomputable def val (x : ℕ) : ℝ := (x:ℝ) / D

lemma D_pos : (0:ℝ) < D := by unfold D; positivity

lemma val_nonneg (x : ℕ) : 0 ≤ val x := by unfold val; have := D_pos; positivity

lemma floor_le (a b : ℕ) : ((a / b : ℕ) : ℝ) ≤ (a:ℝ) / b := Nat.cast_div_le

lemma cdiv_ge (a b : ℕ) (hb : 0 < b) : (a:ℝ) / b ≤ (cdiv a b : ℝ) := by
  unfold cdiv
  have h1 := Nat.div_add_mod (a + b - 1) b
  have h2 := Nat.mod_lt (a + b - 1) hb
  have h3 : a ≤ b * ((a + b - 1) / b) := by omega
  have hb' : (0:ℝ) < b := by exact_mod_cast hb
  rw [div_le_iff₀ hb']
  have : (a:ℝ) ≤ (b * ((a + b - 1) / b) : ℕ) := by exact_mod_cast h3
  push_cast at this; linarith

lemma val_fdivL (a b : ℕ) : val (fdivL a b) ≤ (a:ℝ) / b := by
  unfold val fdivL
  have := floor_le (a * D) b
  have hD := D_pos
  rw [div_le_iff₀ hD]; push_cast at this
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; simp
  have hb' : (0:ℝ) < b := by exact_mod_cast hb
  calc ((a * D / b : ℕ) : ℝ) ≤ a * D / b := this
    _ = a / b * D := by ring

lemma val_fdivU (a b : ℕ) (hb : 0 < b) : (a:ℝ) / b ≤ val (fdivU a b) := by
  unfold val fdivU
  have := cdiv_ge (a * D) b hb
  have hD := D_pos
  rw [le_div_iff₀ hD]; push_cast at this
  calc (a:ℝ) / b * D = a * D / b := by ring
    _ ≤ _ := this

lemma val_fmulL (x y : ℕ) : val (fmulL x y) ≤ val x * val y := by
  unfold val fmulL
  have := floor_le (x * y) D
  have hD := D_pos
  push_cast at this
  rw [div_le_iff₀ hD]
  calc ((x * y / D : ℕ) : ℝ) ≤ x * y / D := this
    _ = x / D * (y / D) * D := by field_simp

lemma val_fmulU (x y : ℕ) : val x * val y ≤ val (fmulU x y) := by
  unfold val fmulU
  have := cdiv_ge (x * y) D (by unfold D; positivity)
  have hD := D_pos
  push_cast at this
  rw [le_div_iff₀ hD]
  calc (x:ℝ) / D * (y / D) * D = x * y / D := by field_simp
    _ ≤ _ := this

lemma val_add (x y : ℕ) : val (x + y) = val x + val y := by unfold val; push_cast; ring

lemma val_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ) : val (∑ i ∈ s, f i) = ∑ i ∈ s, val (f i) := by
  unfold val; push_cast; rw [Finset.sum_div]

lemma val_le {x y : ℕ} (h : x ≤ y) : val x ≤ val y := by
  unfold val; have := D_pos; gcongr

lemma val_lt {x y : ℕ} (h : x < y) : val x < val y := by
  unfold val; have := D_pos; gcongr

lemma val_sub_le (x y : ℕ) : val x - val y ≤ val (x - y) := by
  unfold val
  have hD := D_pos
  rw [← sub_div]; gcongr
  rcases le_total y x with h | h
  · push_cast [h]; linarith
  · rw [Nat.sub_eq_zero_of_le h]; push_cast; linarith [(Nat.cast_le (α := ℝ)).mpr h]

lemma L2lo_le : val L2lo ≤ Real.log 2 := by
  have := val_fdivL 6931471803 (10^10)
  have h2 := Real.log_two_gt_d9
  unfold L2lo; norm_num at this ⊢
  linarith

lemma L2hi_ge : Real.log 2 ≤ val L2hi := by
  have := val_fdivU 6931471808 (10^10) (by norm_num)
  have h2 := Real.log_two_lt_d9
  unfold L2hi; norm_num at this ⊢
  linarith

lemma logLo_le (Q r s : ℕ) (hQ : 0 < Q) (hs : 0 < s) (hrs : s ≤ r) :
    val (logLo Q r s) ≤ Real.log ((r:ℝ) / s) := by
  have hs' : (0:ℝ) < s := by exact_mod_cast hs
  have hr' : (0:ℝ) < r := by exact_mod_cast (lt_of_lt_of_le hs hrs)
  have hrs' : (1:ℝ) ≤ (r:ℝ) / s := by rw [le_div_iff₀ hs']; simp; exact_mod_cast hrs
  have hlog0 : 0 ≤ Real.log ((r:ℝ)/s) := Real.log_nonneg hrs'
  unfold logLo
  split_ifs with hk
  swap
  · simpa [val] using hlog0
  generalize blog2 (powN Q r s) = k at hk ⊢
  simp only [powN, Nat.pow_eq] at hk
  have hk' : (2:ℝ)^k ≤ ((r:ℝ)/s)^Q := by
    have h1 : ((2^k : ℕ):ℝ) ≤ ((r^Q / s^Q : ℕ) : ℝ) := by
      exact_mod_cast hk
    have h2 := floor_le (r^Q) (s^Q)
    push_cast at h1 h2
    rw [div_pow]; linarith
  have hlog : (k:ℝ) * Real.log 2 ≤ Q * Real.log ((r:ℝ)/s) := by
    have := Real.log_le_log (by positivity) hk'
    rwa [Real.log_pow, Real.log_pow] at this
  have hQ' : (0:ℝ) < Q := by exact_mod_cast hQ
  have hf := floor_le (k * L2lo) Q
  unfold val at hf ⊢
  have hL := L2lo_le; unfold val at hL
  have hD := D_pos
  push_cast at hf
  have h3 : ((k * L2lo / Q : ℕ) : ℝ) / D ≤ k * (L2lo / D) / Q := by
    rw [div_le_iff₀ hD]
    calc ((k * L2lo / Q : ℕ) : ℝ) ≤ k * L2lo / Q := hf
      _ = k * (L2lo / D) / Q * D := by field_simp
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have h4 : (k:ℝ) * (L2lo / D) / Q ≤ k * Real.log 2 / Q := by gcongr
  calc _ ≤ _ := h3
    _ ≤ k * Real.log 2 / Q := h4
    _ ≤ Real.log ((r:ℝ)/s) := by rw [div_le_iff₀ hQ']; linarith

lemma logHi_ge (Q r s : ℕ) (hQ : 0 < Q) (hs : 0 < s) (hr : 0 < r) :
    Real.log ((r:ℝ) / s) ≤ val (logHi Q r s) := by
  have hs' : (0:ℝ) < s := by exact_mod_cast hs
  have hr' : (0:ℝ) < r := by exact_mod_cast hr
  unfold logHi
  split_ifs with hk
  swap
  · have h1 := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < (r:ℝ)/s)
    have h2 : (r:ℝ)/s ≤ r := div_le_self hr'.le (by exact_mod_cast hs)
    unfold val; push_cast; rw [mul_div_assoc, div_self D_pos.ne']; linarith
  generalize blog2 (powN Q r s) = k at hk ⊢
  simp only [powN, Nat.pow_eq] at hk
  have hspos : 0 < s^Q := by positivity
  have hk2 : r^Q < 2^(k+1) * s^Q := by
    rw [← Nat.div_lt_iff_lt_mul hspos]; simpa using hk
  have hk' : ((r:ℝ)/s)^Q ≤ (2:ℝ)^(k+1) := by
    have : ((r^Q : ℕ):ℝ) ≤ ((2^(k+1) * s^Q : ℕ) : ℝ) := by exact_mod_cast hk2.le
    push_cast at this
    rw [div_pow, div_le_iff₀ (by positivity)]; linarith
  have hlog : Q * Real.log ((r:ℝ)/s) ≤ (k+1:ℕ) * Real.log 2 := by
    have := Real.log_le_log (by positivity) hk'
    rwa [Real.log_pow, Real.log_pow] at this
  have hQ' : (0:ℝ) < Q := by exact_mod_cast hQ
  have hc := cdiv_ge ((k+1) * L2hi) Q hQ
  have hL := L2hi_ge
  unfold val at hL ⊢
  have hD := D_pos
  push_cast at hc hlog
  rw [le_div_iff₀ hD]
  have h1 : Real.log ((r:ℝ)/s) ≤ (k+1) * (L2hi / D) / Q := by
    rw [le_div_iff₀ hQ']
    have : ((k:ℝ)+1) * Real.log 2 ≤ (k+1) * (L2hi / D) := by gcongr
    linarith
  calc Real.log ((r:ℝ)/s) * D ≤ (k+1) * (L2hi / D) / Q * D := by gcongr
    _ = ((k:ℝ)+1) * L2hi / Q := by field_simp
    _ ≤ _ := hc

lemma mlog_hasSum (x : ℝ) (h0 : 0 ≤ x) (h1 : x < 1) :
    HasSum (fun n : ℕ => x ^ (n + 1) / (n + 1)) (-Real.log (1 - x)) :=
  Real.hasSum_pow_div_log_of_abs_lt_one (by rw [abs_of_nonneg h0]; exact h1)

lemma mlogLo_le (u v n : ℕ) (huv : u < v) :
    val (mlogLo u v n) ≤ -Real.log (1 - (u:ℝ)/v) := by
  have hv : (0:ℝ) < v := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le u) huv)
  have hx0 : 0 ≤ (u:ℝ)/v := by positivity
  have hx1 : (u:ℝ)/v < 1 := by rw [div_lt_one hv]; exact_mod_cast huv
  have hs := mlog_hasSum _ hx0 hx1
  have h := sum_le_hasSum (range n) (fun i _ => by positivity) hs
  refine le_trans ?_ h
  unfold mlogLo
  rw [val_sum]
  apply Finset.sum_le_sum
  intro i _
  refine (val_fdivL _ _).trans (le_of_eq ?_)
  push_cast; rw [div_pow]; field_simp

lemma mlogHi_ge (u v n : ℕ) (huv : u < v) :
    -Real.log (1 - (u:ℝ)/v) ≤ val (mlogHi u v n) := by
  have hv0 : 0 < v := lt_of_le_of_lt (Nat.zero_le u) huv
  have hv : (0:ℝ) < v := by exact_mod_cast hv0
  have hx0 : 0 ≤ (u:ℝ)/v := by positivity
  have hx1 : (u:ℝ)/v < 1 := by rw [div_lt_one hv]; exact_mod_cast huv
  have habs : |(u:ℝ)/v| < 1 := by rw [abs_of_nonneg hx0]; exact hx1
  have h := Real.abs_log_sub_add_sum_range_le habs n
  rw [abs_of_nonneg hx0] at h
  have h' := (abs_le.mp h).1
  unfold mlogHi
  rw [val_add, val_sum]
  have hvu : 0 < v - u := Nat.sub_pos_of_lt huv
  have hR : ((u:ℝ)/v) ^ (n+1) / (1 - (u:ℝ)/v) ≤ val (fdivU (u^(n+1)) (v^n * (v - u))) := by
    refine le_trans (le_of_eq ?_) (val_fdivU _ _ (by positivity))
    have : ((v - u : ℕ) : ℝ) = v - u := by push_cast [huv.le]; ring
    push_cast [huv.le]
    have : (v:ℝ) - u ≠ 0 := by
      have : (u:ℝ) < v := by exact_mod_cast huv
      linarith
    have hvne : (v:ℝ) ≠ 0 := hv.ne'
    rw [div_pow, div_div, eq_div_iff (by positivity)]
    field_simp
    ring
  have hS : ∑ i ∈ range n, ((u:ℝ)/v) ^ (i + 1) / (i + 1)
      ≤ ∑ i ∈ range n, val (fdivU (u^(i+1)) (v^(i+1) * (i+1))) := by
    apply Finset.sum_le_sum
    intro i _
    refine le_trans (le_of_eq ?_) (val_fdivU _ _ (by positivity))
    push_cast; rw [div_pow]; field_simp
  linarith

attribute [irreducible] blog2 logLo logHi

end RobinFix


-- ===== Gam =====

set_option autoImplicit false
open Finset

namespace RobinFix

def GAM : ℕ := 10645318814745900000

lemma sum_blocks {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ k ∈ range (64 * m), f k = ∑ j ∈ range m, ∑ i ∈ range 64, f (64 * j + i) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 64 * (m+1) = 64 * m + 64 by ring, Finset.sum_range_add, ih,
      Finset.sum_range_succ (fun j => ∑ i ∈ range 64, f (64 * j + i)) m]

lemma GAM_cert' : GAM + logHi 65536 4097 1 ≤
    ∑ j ∈ range 64, ∑ i ∈ range 64, fdivL 1 (64 * j + i + 1) := by
  decide +kernel

lemma GAM_le_aux (X : ℕ) (hX : GAM + X ≤ ∑ j ∈ range 64, ∑ i ∈ range 64, fdivL 1 (64 * j + i + 1))
    (h2 : Real.log 4097 ≤ val X) : val GAM < Real.eulerMascheroniConstant := by
  have h1 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 4096
  unfold Real.eulerMascheroniSeq harmonic at h1
  rw [show (4096:ℕ) = 64 * 64 from rfl, sum_blocks] at h1
  have h3 : val GAM + val X ≤ ∑ j ∈ range 64, ∑ i ∈ range 64, val (fdivL 1 (64 * j + i + 1)) := by
    rw [← val_add]; simp only [← val_sum]; exact val_le hX
  have h4 : ∑ j ∈ range 64, ∑ i ∈ range 64, val (fdivL 1 (64 * j + i + 1)) ≤
      ∑ j ∈ range 64, ∑ i ∈ range 64, (1:ℝ) / ((64 * j + i + 1 : ℕ):ℝ) :=
    Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun i _ => by simpa using val_fdivL 1 (64 * j + i + 1)))
  push_cast at h1 h4
  simp only [one_div] at h4
  norm_num at h1
  linarith

lemma GAM_le : val GAM < Real.eulerMascheroniConstant := by
  have h2 := logHi_ge 65536 4097 1 (by norm_num) one_pos (by norm_num)
  rw [Nat.cast_one, div_one] at h2
  exact GAM_le_aux _ GAM_cert' (by exact_mod_cast h2)

end RobinFix

-- ===== Direct =====

set_option autoImplicit false
open Finset

namespace RobinFix

def fastSigma (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, ∑ i ∈ Finset.range (n.primeFactorsList.count p + 1), p ^ i

lemma sigma_eq_fast (n : ℕ) (hn : n ≠ 0) : ArithmeticFunction.sigma 1 n = fastSigma n := by
  simpa [fastSigma] using
    ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul (k := 1) hn

lemma exp_gamma_ge : (1.7808:ℝ) ≤ Real.exp Real.eulerMascheroniConstant := by
  have hg := GAM_le
  have hv : (0.577083:ℝ) ≤ val GAM := by
    unfold val GAM; rw [le_div_iff₀ D_pos]; unfold D; norm_num
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 0.577083) 8
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have := Real.exp_le_exp.mpr (le_of_lt (lt_of_le_of_lt hv hg))
  linarith

def blockOK (N1 N2 : ℕ) : Bool :=
  let LL := logLo QL (logLo QL N1 1) D
  decide (5041 ≤ N1) && decide (D ≤ logLo QL N1 1) &&
  (List.range' N1 (N2 - N1)).all (fun n => decide (fastSigma n * D * 10000 < 17808 * n * LL))

lemma blockOK_sound (N1 N2 : ℕ) (h : blockOK N1 N2 = true) (n : ℕ) (h1 : N1 ≤ n) (h2 : n < N2) :
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) <
      Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by
  unfold blockOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range'] at h
  obtain ⟨⟨hN, hD⟩, hall⟩ := h
  have hc := hall n ⟨n - N1, by omega, by omega⟩
  have hn0 : n ≠ 0 := by omega
  rw [sigma_eq_fast n hn0]
  set lA := logLo QL N1 1
  have hN0 : (0:ℝ) < N1 := by exact_mod_cast (by omega : 0 < N1)
  have hnr : (N1:ℝ) ≤ n := by exact_mod_cast h1
  have hn0' : (0:ℝ) < n := by linarith
  have hDpos : 0 < D := by unfold D; norm_num
  have hlA : val lA ≤ Real.log N1 := by
    have := logLo_le QL N1 1 (by unfold QL; norm_num) one_pos (by omega)
    simpa using this
  have hlA1 : 0 < val lA := by unfold val; exact div_pos (by exact_mod_cast lt_of_lt_of_le hDpos hD) D_pos
  have hll : val (logLo QL lA D) ≤ Real.log (Real.log n) := by
    have := logLo_le QL lA D (by unfold QL; norm_num) hDpos hD
    have e : ((lA:ℝ) / D) = val lA := rfl
    rw [e] at this
    exact this.trans (Real.log_le_log hlA1 (hlA.trans (Real.log_le_log hN0 hnr)))
  have hc' : ((fastSigma n * D * 10000 : ℕ) : ℝ) < ((17808 * n * logLo QL lA D : ℕ) : ℝ) := by
    exact_mod_cast hc
  push_cast at hc'
  have hD' := D_pos
  have key : (fastSigma n : ℝ) < 1.7808 * n * val (logLo QL lA D) := by
    unfold val
    rw [show (1.7808:ℝ) * n * ((logLo QL lA D : ℕ) / (D:ℝ)) = 17808 * n * (logLo QL lA D : ℕ) / (D * 10000) by
      field_simp; ring]
    rw [lt_div_iff₀ (by positivity)]; linarith
  have hE := exp_gamma_ge
  calc (fastSigma n : ℝ) < 1.7808 * n * val (logLo QL lA D) := key
    _ ≤ Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by
      have h0 := val_nonneg (logLo QL lA D)
      apply mul_le_mul (mul_le_mul_of_nonneg_right hE hn0'.le) hll h0 (by positivity)

end RobinFix

-- ===== Cover =====

set_option autoImplicit false

namespace RobinFix

def chainOK : List (ℕ × ℕ) → ℕ → ℕ → Bool
  | [], s, e => decide (e ≤ s)
  | (a, b) :: L, s, e => decide (a = s) && chainOK L b e

lemma cover (L : List (ℕ × ℕ)) (s e : ℕ) (h : chainOK L s e = true) (c : ℝ) (hc : 0 < c)
    (x : ℝ) (hx1 : (s:ℝ) / c ≤ x) (hx2 : x < (e:ℝ) / c) :
    ∃ p ∈ L, (p.1:ℝ) / c ≤ x ∧ x < (p.2:ℝ) / c := by
  induction L generalizing s with
  | nil =>
    simp only [chainOK, decide_eq_true_eq] at h
    have : (e:ℝ) ≤ s := by exact_mod_cast h
    have : (e:ℝ) / c ≤ s / c := div_le_div_of_nonneg_right this hc.le
    linarith
  | cons q L ih =>
    obtain ⟨a, b⟩ := q
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, h⟩ := h
    by_cases hb : x < (b:ℝ) / c
    · exact ⟨(a, b), List.mem_cons_self .., hx1, hb⟩
    · obtain ⟨p, hp, hp1, hp2⟩ := ih b h (by linarith) 
      exact ⟨p, List.mem_cons_of_mem _ hp, hp1, hp2⟩

end RobinFix

-- ===== PubDirect2 =====

set_option autoImplicit false

namespace RobinFix

def blocks_11041 : List (ℕ × ℕ) := [(11041,12041),(12041,13041),(13041,14041),(14041,15041),(15041,16041),(16041,17041)]

lemma blocks_11041_chain : chainOK blocks_11041 11041 17041 = true := by decide +kernel

lemma blocks_11041_ok : blocks_11041.all (fun b => blockOK b.1 b.2) = true := by decide +kernel

end RobinFix

namespace RobinRHParts

theorem robin_direct_11041_17041 : ∀ n : ℕ, 11041 ≤ n → n < 17041 →
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by
  intro n h1 h2
  obtain ⟨p, hp, hp1, hp2⟩ := RobinFix.cover RobinFix.blocks_11041 11041 17041 RobinFix.blocks_11041_chain 1 one_pos
    (n:ℝ) (by simp only [div_one]; exact_mod_cast h1) (by simp only [div_one]; exact_mod_cast h2)
  simp only [div_one] at hp1 hp2
  exact RobinFix.blockOK_sound p.1 p.2 (List.all_eq_true.mp RobinFix.blocks_11041_ok p hp) n
    (by exact_mod_cast hp1) (by exact_mod_cast hp2)

end RobinRHParts

theorem solution :
    ∀ n : ℕ, 11041 ≤ n → n < 17041 →
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) :=
  RobinRHParts.robin_direct_11041_17041
