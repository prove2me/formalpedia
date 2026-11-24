-- Prove2me | solution 1 for RobinRHParts.robin_RH_logrange_1000_1100000
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-24T03:17:18.268121+00:00
-- url     : https://prove2.me/submissions/6863e0a9-62a7-4cc0-a772-d3a5a7d9cbea

import Theorems.Thm_ArtinPrimitiveRoots_mertens_product
import Theorems.Thm_LandauCriterion_sum_multiplicity_div_normSq_zeros_le
import Theorems.Thm_MasulloRH_prime_ramp_integrated_explicit_formula
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_psi_le
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_low
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_mid
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_high
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


-- ===== Local =====

set_option autoImplicit false
open Finset

namespace RobinRH

noncomputable def eps (t : ℝ) : ℝ := Real.log (1 + 1/t) / Real.log t

lemma cast_pos2 (p : ℕ) (hp : 2 ≤ p) : (0:ℝ) < p := by
  have : (2:ℝ) ≤ p := by exact_mod_cast hp
  linarith

noncomputable def S (p : ℕ) (a : ℕ) : ℝ := ∑ i ∈ range (a+1), (p:ℝ)^i

lemma S_succ (p a : ℕ) : S p (a+1) = p * S p a + 1 := by
  unfold S
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp [pow_succ]
  apply Finset.sum_congr rfl; intro i _; ring

lemma S_ge_one (p a : ℕ) : 1 ≤ S p a := by
  unfold S
  rw [Finset.sum_range_succ']
  simp only [pow_zero]
  have : 0 ≤ ∑ i ∈ range a, (p:ℝ)^(i+1) := Finset.sum_nonneg (fun i _ => by positivity)
  linarith

lemma S_pos (p a : ℕ) : 0 < S p a := lt_of_lt_of_le one_pos (S_ge_one p a)

lemma S_zero (p : ℕ) : S p 0 = 1 := by simp [S]

lemma S_mul (p a : ℕ) : S p a * ((p:ℝ) - 1) = (p:ℝ)^(a+1) - 1 := by
  induction a with
  | zero => simp [S]
  | succ a ih => rw [S_succ]; rw [show ((p:ℝ) * S p a + 1) * ((p:ℝ) - 1) =
        p * (S p a * ((p:ℝ) - 1)) + (p - 1) by ring, ih]; ring

lemma S_le_pow (p a : ℕ) : S p a ≤ ((p:ℝ) + 1)^a := by
  induction a with
  | zero => simp [S]
  | succ a ih =>
    rw [S_succ, pow_succ]
    have h1 : 1 ≤ ((p:ℝ)+1)^a := one_le_pow₀ (by linarith [(Nat.cast_nonneg p : (0:ℝ) ≤ p)])
    have hp : (0:ℝ) ≤ p := Nat.cast_nonneg p
    nlinarith

/-- `T p a = log (S_a / p^a)`. -/
noncomputable def T (p a : ℕ) : ℝ := Real.log (S p a / (p:ℝ)^a)

lemma T_zero (p : ℕ) : T p 0 = 0 := by simp [T, S]

/-- increments -/
lemma T_succ_sub_ge (p a : ℕ) (hp : 2 ≤ p) :
    1 / S p (a+1) ≤ T p (a+1) - T p a := by
  have hp0 : (0:ℝ) < p := cast_pos2 p hp
  have hS := S_pos p a
  have hS1 := S_pos p (a+1)
  unfold T
  rw [← Real.log_div (by positivity) (by positivity)]
  have e : S p (a+1) / (p:ℝ)^(a+1) / (S p a / (p:ℝ)^a) = S p (a+1) / (p * S p a) := by
    field_simp; ring
  rw [e]
  have hl := Real.one_sub_inv_le_log_of_pos (show 0 < S p (a+1) / (p * S p a) by positivity)
  have e2 : 1 - (S p (a+1) / (p * S p a))⁻¹ = 1 / S p (a+1) := by
    rw [S_succ]; field_simp; ring
  linarith

lemma T_le (p a : ℕ) (hp : 2 ≤ p) : T p a ≤ -Real.log (1 - 1/(p:ℝ)) := by
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0:ℝ) < p := by linarith
  have hS := S_pos p a
  have hq : 0 < 1 - 1/(p:ℝ) := by rw [sub_pos, div_lt_one hp0]; linarith
  unfold T
  rw [← Real.log_inv]
  apply Real.log_le_log (by positivity)
  have hM := S_mul p a
  rw [div_le_iff₀ (by positivity)]
  have : (1 - 1/(p:ℝ))⁻¹ = p / (p - 1) := by field_simp
  rw [this, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
  have : (p:ℝ)^(a+1) = p * p^a := by ring
  nlinarith [pow_pos hp0 a]

lemma T_one (p : ℕ) (hp : 2 ≤ p) : T p 1 = Real.log (1 + 1/(p:ℝ)) := by
  have hp0 : (0:ℝ) < p := cast_pos2 p hp
  unfold T S
  congr 1
  simp [Finset.sum_range_succ]
  field_simp
  ring

lemma T_le_mul (p a : ℕ) (hp : 2 ≤ p) : T p a ≤ a * Real.log (1 + 1/(p:ℝ)) := by
  have hp0 : (0:ℝ) < p := cast_pos2 p hp
  unfold T
  rw [← Real.log_pow]
  apply Real.log_le_log (div_pos (S_pos p a) (by positivity))
  rw [div_le_iff₀ (by positivity), ← mul_pow]
  have : (1 + 1/(p:ℝ)) * p = p + 1 := by field_simp
  rw [this]; exact S_le_pow p a


lemma T_eq_sum (p a : ℕ) : T p a = ∑ i ∈ range a, (T p (i+1) - T p i) := by
  rw [Finset.sum_range_sub, T_zero, sub_zero]

theorem prime_bound_small (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : c ≤ Real.log (1 + 1/(p:ℝ))) (J a : ℕ) :
    T p a - a * c ≤ -Real.log (1 - 1/(p:ℝ)) - c - ∑ i ∈ Ico 1 J, min (1 / S p (i+1)) c := by
  set m := max a J + 1 with hm
  set D : ℕ → ℝ := fun i => T p (i+1) - T p i with hD
  have hTm := T_le p m hp
  have hA : ∑ i ∈ range m, (if i < a then D i - c else 0) = T p a - a * c := by
    rw [← Finset.sum_filter]
    have : (range m).filter (fun i => i < a) = range a := by
      ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [this, Finset.sum_sub_distrib, T_eq_sum]; simp [hD, Finset.sum_sub_distrib]
  have hB : ∑ i ∈ range m, (if i = 0 then c else 0) = c := by
    rw [Finset.sum_ite_eq']; simp [hm]
  have hC : ∑ i ∈ range m, (if i ∈ Ico 1 J then min (1 / S p (i+1)) c else 0) =
      ∑ i ∈ Ico 1 J, min (1 / S p (i+1)) c := by
    rw [Finset.sum_ite_mem]
    congr 1
    ext i; simp only [Finset.mem_inter, Finset.mem_range, Finset.mem_Ico]; omega
  have hsum : ∑ i ∈ range m, ((if i < a then D i - c else 0) + (if i = 0 then c else 0) +
      (if i ∈ Ico 1 J then min (1 / S p (i+1)) c else 0)) ≤ ∑ i ∈ range m, D i := by
    apply Finset.sum_le_sum
    intro i _
    have hge := T_succ_sub_ge p i hp
    have hpos : 0 < 1 / S p (i+1) := by have := S_pos p (i+1); positivity
    have hDi : 1 / S p (i+1) ≤ D i := hge
    have hmin1 : min (1 / S p (i+1)) c ≤ c := min_le_right _ _
    have hmin2 : min (1 / S p (i+1)) c ≤ 1 / S p (i+1) := min_le_left _ _
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0
      have hD0 : D 0 = Real.log (1 + 1/(p:ℝ)) := by
        simp only [hD]; rw [T_one p hp, T_zero]; ring
      have hn : (0:ℕ) ∉ Ico 1 J := by simp
      simp only [hn, if_false, if_true, add_zero]
      split_ifs <;> linarith
    · have hn0 : i ≠ 0 := by omega
      simp only [hn0, if_false, add_zero]
      split_ifs <;> linarith
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hA, hB, hC] at hsum
  have hTs : T p m = ∑ i ∈ range m, D i := T_eq_sum p m
  linarith

theorem prime_bound_large (p : ℕ) (hp : 2 ≤ p) (c : ℝ)
    (hc : Real.log (1 + 1/(p:ℝ)) ≤ c) (a : ℕ) : T p a - a * c ≤ 0 := by
  have h := T_le_mul p a hp
  have : (a:ℝ) * Real.log (1 + 1/(p:ℝ)) ≤ a * c := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg a)
  linarith

/-- `log(1+1/x)/log x` is antitone on `(1,∞)`. -/
lemma ratio_anti (x y : ℝ) (hx : 1 < x) (hxy : x ≤ y) :
    Real.log (1 + 1/y) / Real.log y ≤ Real.log (1 + 1/x) / Real.log x := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hly : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
  have h1 : Real.log (1 + 1/y) ≤ Real.log (1 + 1/x) := by
    apply Real.log_le_log (by positivity)
    have : 1/y ≤ 1/x := one_div_le_one_div_of_le hx0 hxy
    linarith
  have h0 : 0 ≤ Real.log (1 + 1/y) := Real.log_nonneg (by have : 0 ≤ 1/y := by positivity
                                                          linarith)
  calc Real.log (1 + 1/y) / Real.log y ≤ Real.log (1 + 1/y) / Real.log x :=
        div_le_div_of_nonneg_left h0 hlx hly
    _ ≤ Real.log (1 + 1/x) / Real.log x := div_le_div_of_nonneg_right h1 hlx.le


noncomputable def Lf (x : ℝ) : ℝ :=
  ∑ p ∈ (Icc 2 ⌊x⌋₊).filter Nat.Prime, -Real.log (1 - 1/(p:ℝ))

noncomputable def Gf (J : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ (Icc 2 ⌊x⌋₊).filter Nat.Prime, ∑ i ∈ Ico 1 J, min (1 / S p (i+1)) (eps x * Real.log p)

lemma theta_eq_Icc2 (x : ℝ) :
    Chebyshev.theta x = ∑ p ∈ (Icc 2 ⌊x⌋₊).filter Nat.Prime, Real.log p := by
  rw [Chebyshev.theta]
  congr 1
  ext p; simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h3.two_le, h2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by omega, h2⟩, h3⟩

lemma eps_nonneg (t : ℝ) (ht : 1 < t) : 0 ≤ eps t := by
  unfold eps
  apply div_nonneg _ (Real.log_pos ht).le
  apply Real.log_nonneg
  have : 0 ≤ 1/t := by positivity
  linarith

open ArithmeticFunction in
theorem local_bound (J n : ℕ) (hn : 3 ≤ n) :
    Real.log ((sigma 1 n : ℝ) / n) ≤
      eps (Real.log n) * (Real.log n - Chebyshev.theta (Real.log n)) + Lf (Real.log n)
        - Gf J (Real.log n) := by
  set t := Real.log n with ht_def
  have hn0 : n ≠ 0 := by omega
  have ht1 : 1 < t := by
    rw [ht_def, Real.lt_log_iff_exp_lt (by positivity)]
    have := Real.exp_one_lt_d9
    have : (3:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  set e := eps t with he
  have he0 : 0 ≤ e := eps_nonneg t ht1
  set pf := n.primeFactors
  set v := n.factorization
  have hpf : ∀ p ∈ pf, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  -- product formulas
  have hsig : ((sigma 1 n : ℕ) : ℝ) = ∏ p ∈ pf, S p (v p) := by
    rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn0]
    push_cast
    apply Finset.prod_congr rfl
    intro p _
    simp [S, v]
  have hnR : (n:ℝ) = ∏ p ∈ pf, (p:ℝ)^(v p) := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn0]
    push_cast; rfl
  have hlog : Real.log ((sigma 1 n : ℝ) / n) = ∑ p ∈ pf, T p (v p) := by
    rw [hsig, hnR, ← Finset.prod_div_distrib, Real.log_prod]
    · rfl
    · intro p hp
      have := (hpf p hp).two_le
      exact (div_pos (S_pos p (v p)) (pow_pos (cast_pos2 p this) _)).ne'
  have ht_sum : t = ∑ p ∈ pf, (v p : ℝ) * Real.log p := by
    rw [ht_def, hnR, Real.log_prod]
    · apply Finset.sum_congr rfl; intro p _; rw [Real.log_pow]
    · intro p hp; exact (pow_pos (cast_pos2 p (hpf p hp).two_le) _).ne'
  -- per-prime bound
  set B : ℕ → ℝ := fun p => -Real.log (1 - 1/(p:ℝ)) - e * Real.log p -
    ∑ i ∈ Ico 1 J, min (1 / S p (i+1)) (e * Real.log p) with hB
  have hsmall : ∀ p : ℕ, p.Prime → p ≤ ⌊t⌋₊ → ∀ a : ℕ, T p a - a * (e * Real.log p) ≤ B p := by
    intro p hp hpt a
    have hp2 := hp.two_le
    have hp1 : (1:ℝ) < p := by have : (2:ℝ) ≤ p := by exact_mod_cast hp2
                               linarith
    have hpt' : (p:ℝ) ≤ t := le_trans (by exact_mod_cast hpt) (Nat.floor_le (by linarith))
    have hlp : 0 < Real.log p := Real.log_pos hp1
    have hr := ratio_anti p t hp1 hpt'
    have hc : e * Real.log p ≤ Real.log (1 + 1/(p:ℝ)) := by
      rw [he]; unfold eps
      calc Real.log (1 + 1/t) / Real.log t * Real.log p ≤
            Real.log (1 + 1/(p:ℝ)) / Real.log p * Real.log p :=
              mul_le_mul_of_nonneg_right hr hlp.le
        _ = _ := by field_simp
    exact prime_bound_small p hp2 _ (mul_nonneg he0 hlp.le) hc J a
  have hlarge : ∀ p : ℕ, p.Prime → ⌊t⌋₊ < p → ∀ a : ℕ, T p a - a * (e * Real.log p) ≤ 0 := by
    intro p hp hpt a
    have hp2 := hp.two_le
    have hpt' : t < (p:ℝ) := (Nat.floor_lt (by linarith)).mp hpt
    have hp1 : (1:ℝ) < p := by linarith
    have hlp : 0 < Real.log p := Real.log_pos hp1
    have hr := ratio_anti t p ht1 hpt'.le
    have hc : Real.log (1 + 1/(p:ℝ)) ≤ e * Real.log p := by
      rw [he]; unfold eps
      calc Real.log (1 + 1/(p:ℝ)) = Real.log (1 + 1/(p:ℝ)) / Real.log p * Real.log p := by
            field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hr hlp.le
    exact prime_bound_large p hp2 _ hc a
  have hBnn : ∀ p : ℕ, p.Prime → p ≤ ⌊t⌋₊ → 0 ≤ B p := by
    intro p hp hpt
    have := hsmall p hp hpt 0
    simp [T_zero] at this
    linarith
  set Pt := (Icc 2 ⌊t⌋₊).filter Nat.Prime
  have hstep1 : ∑ p ∈ pf, (T p (v p) - (v p : ℝ) * (e * Real.log p)) ≤
      ∑ p ∈ pf, (if p ≤ ⌊t⌋₊ then B p else 0) := by
    apply Finset.sum_le_sum
    intro p hp
    split_ifs with h
    · exact hsmall p (hpf p hp) h _
    · exact hlarge p (hpf p hp) (by omega) _
  have hstep2 : ∑ p ∈ pf, (if p ≤ ⌊t⌋₊ then B p else 0) ≤ ∑ p ∈ Pt, B p := by
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [Finset.mem_filter] at hp
      simp only [Pt, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨(hpf p hp.1).two_le, hp.2⟩, hpf p hp.1⟩
    · intro p hp _
      simp only [Pt, Finset.mem_filter, Finset.mem_Icc] at hp
      exact hBnn p hp.2 hp.1.2
  have hstep3 : ∑ p ∈ Pt, B p = Lf t - e * Chebyshev.theta t - Gf J t := by
    simp only [hB, Finset.sum_sub_distrib, Lf, Gf, theta_eq_Icc2, Finset.mul_sum, ← he, Pt]
  have hsplit : ∑ p ∈ pf, T p (v p) = e * t +
      ∑ p ∈ pf, (T p (v p) - (v p : ℝ) * (e * Real.log p)) := by
    rw [Finset.sum_sub_distrib, ht_sum, Finset.mul_sum]
    have : ∑ p ∈ pf, (v p : ℝ) * (e * Real.log p) = ∑ p ∈ pf, e * ((v p : ℝ) * Real.log p) := by
      apply Finset.sum_congr rfl; intro p _; ring
    rw [this]; ring
  rw [hlog, hsplit]
  linarith

end RobinRH

-- ===== GFix =====

set_option autoImplicit false
open Finset

namespace RobinFix
open RobinRH

def primeB (n : ℕ) : Bool :=
  decide (2 ≤ n) && (List.range 65).all (fun d => d < 2 || n < d*d || n % d != 0)

lemma primeB_iff (n : ℕ) (hn : n < 4225) : primeB n = true ↔ n.Prime := by
  unfold primeB
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨h2, hall⟩
    by_contra hnp
    have hm := Nat.minFac_sq_le_self (by omega) hnp
    have hmp : (Nat.minFac n).Prime := Nat.minFac_prime (by omega)
    have hm2 := hmp.two_le
    have hm65 : Nat.minFac n < 65 := by
      by_contra h; push_neg at h; nlinarith
    have := hall (Nat.minFac n) hm65
    rcases this with (h | h) | h
    · omega
    · nlinarith
    · exact h (Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd n))
  · intro hp
    refine ⟨hp.two_le, fun d _ => ?_⟩
    by_cases hd : d < 2
    · left; left; simpa using hd
    by_cases hdd : n < d * d
    · left; right; simpa using hdd
    right
    intro h0
    have hdvd : d ∣ n := Nat.dvd_of_mod_eq_zero h0
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · omega
    · subst h1; push_neg at hdd; nlinarith [hp.two_le]

def sumP (g : ℕ → ℕ) (P : ℕ) : ℕ := ∑ p ∈ range (P+1), if primeB p then g p else 0

lemma sum_filter_eq (F : ℕ → ℝ) (P : ℕ) :
    ∑ p ∈ (Icc 2 P).filter Nat.Prime, F p = ∑ p ∈ range (P+1), if p.Prime then F p else 0 := by
  rw [Finset.sum_filter]
  apply Finset.sum_subset
  · intro p hp; simp at hp ⊢; omega
  · intro p hp hn
    simp at hp hn
    have : ¬ p.Prime := by
      intro h; have := h.two_le; exact absurd (hn this) (by omega)
    simp [this]

lemma sumP_le (g : ℕ → ℕ) (F : ℕ → ℝ) (P : ℕ) (hP : P < 4225)
    (h : ∀ p, p.Prime → p ≤ P → val (g p) ≤ F p) :
    val (sumP g P) ≤ ∑ p ∈ (Icc 2 P).filter Nat.Prime, F p := by
  rw [sum_filter_eq, sumP, val_sum]
  apply Finset.sum_le_sum
  intro p hp
  simp only [mem_range] at hp
  have hb := primeB_iff p (by omega)
  by_cases hpr : p.Prime
  · have : primeB p = true := hb.mpr hpr
    simp only [this, hpr, if_true]; exact h p hpr (by omega)
  · have : primeB p = false := by
      cases h' : primeB p
      · rfl
      · exact absurd (hb.mp h') hpr
    simp [this, hpr, val]

lemma sumP_ge (g : ℕ → ℕ) (F : ℕ → ℝ) (P : ℕ) (hP : P < 4225)
    (h : ∀ p, p.Prime → p ≤ P → F p ≤ val (g p)) :
    ∑ p ∈ (Icc 2 P).filter Nat.Prime, F p ≤ val (sumP g P) := by
  rw [sum_filter_eq, sumP, val_sum]
  apply Finset.sum_le_sum
  intro p hp
  simp only [mem_range] at hp
  have hb := primeB_iff p (by omega)
  by_cases hpr : p.Prime
  · have : primeB p = true := hb.mpr hpr
    simp only [this, hpr, if_true]; exact h p hpr (by omega)
  · have : primeB p = false := by
      cases h' : primeB p
      · rfl
      · exact absurd (hb.mp h') hpr
    simp [this, hpr, val]


def SN (p j : ℕ) : ℕ := ∑ i ∈ range (j+1), p^i

lemma SN_cast (p j : ℕ) : ((SN p j : ℕ) : ℝ) = S p j := by
  unfold SN S; push_cast; rfl

def gtermN (e p : ℕ) : ℕ := ∑ i ∈ Ico 1 8, min (fdivL 1 (SN p (i+1))) (fmulL e (logLo QL p 1))

def GN (e P : ℕ) : ℕ := sumP (gtermN e) P

lemma val_min (a b : ℕ) : val (min a b) = min (val a) (val b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (val_le h)]
  · rw [min_eq_right h, min_eq_right (val_le h)]

lemma logLo_prime_le (p : ℕ) (hp : 1 ≤ p) : val (logLo QL p 1) ≤ Real.log p := by
  have := logLo_le QL p 1 (by unfold QL; norm_num) one_pos hp
  simpa using this

lemma gtermN_le (e p : ℕ) (hp : p.Prime) (t : ℝ) (he : val e ≤ eps t) :
    val (gtermN e p) ≤ ∑ i ∈ Ico 1 8, min (1 / S p (i+1)) (eps t * Real.log p) := by
  unfold gtermN
  rw [val_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [val_min]
  apply min_le_min
  · refine (val_fdivL _ _).trans (le_of_eq ?_)
    rw [SN_cast]; simp
  · refine (val_fmulL _ _).trans ?_
    exact mul_le_mul he (logLo_prime_le p hp.one_lt.le) (val_nonneg _)
      ((val_nonneg e).trans he)

lemma GN_le (e P : ℕ) (hP : P < 4225) (t : ℝ) (ht : 1 < t) (hPt : P ≤ ⌊t⌋₊)
    (he : val e ≤ eps t) : val (GN e P) ≤ Gf 8 t := by
  refine (sumP_le _ _ P hP (fun p hp _ => gtermN_le e p hp t he)).trans ?_
  unfold Gf
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp; simp only [mem_filter, mem_Icc] at hp ⊢; exact ⟨⟨hp.1.1, by omega⟩, hp.2⟩
  · intro p hp _
    apply Finset.sum_nonneg
    intro i _
    have hp2 := (Finset.mem_filter.mp hp).2.two_le
    apply le_min
    · have := S_pos p (i+1); positivity
    · exact mul_nonneg (eps_nonneg t ht) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p)))

end RobinFix

-- ===== RH =====

set_option autoImplicit false
open Finset ArithmeticFunction MeasureTheory Filter Topology



namespace NicCore

noncomputable def Mfun (x : ℝ) : ℝ :=
  ((∑ n ∈ range (⌊x⌋₊+1), vonMangoldt n * max (x/(n:ℝ)-1) 0) -
      x*(Real.log x-1-Real.eulerMascheroniConstant)) / x

noncomputable def βc : ℝ := 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)

noncomputable def Kt (x : ℝ) (ρ : MasulloRH.ZetaZerosInTraceStrip (1/2)) : ℂ :=
  (analyticOrderNatAt riemannZeta ρ.val : ℂ) * (x:ℂ)^(ρ.val-1)/(ρ.val*(ρ.val-1))

lemma re_half (hRH : RiemannHypothesis) (ρ : MasulloRH.ZetaZerosInTraceStrip (1/2)) :
    ρ.val.re = 1/2 := by
  obtain ⟨hz, h0, h1, -⟩ := ρ.property
  apply hRH ρ.val hz
  · rintro ⟨n, hn⟩
    have : ρ.val.re = -2 * ((n:ℝ) + 1) := by rw [hn]; simp
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · intro h; rw [h] at h1; simp at h1

lemma norm_Kt (hRH : RiemannHypothesis) (x : ℝ) (hx : 0 < x)
    (ρ : MasulloRH.ZetaZerosInTraceStrip (1/2)) :
    ‖Kt x ρ‖ = x ^ (-(1/2:ℝ)) * ((analyticOrderNatAt riemannZeta ρ.val : ℝ) / ‖ρ.val‖ ^ 2) := by
  have hre := re_half hRH ρ
  have hne : ρ.val ≠ 0 := by
    intro h; rw [h] at hre; simp at hre
  have hn1 : ‖ρ.val - 1‖ = ‖ρ.val‖ := by
    rw [Complex.norm_def, Complex.norm_def]
    congr 1
    simp [Complex.normSq_apply, hre]
    ring
  rw [Kt, norm_div, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, hn1]
  have : (ρ.val - 1).re = -(1/2) := by simp [hre]; norm_num
  rw [this]
  simp only [Complex.norm_natCast]
  have hp : 0 < ‖ρ.val‖ := norm_pos_iff.mpr hne
  field_simp

lemma summable_Kt (x : ℝ) (hx : 1 ≤ x) : Summable (fun ρ => ‖Kt x ρ‖) := by
  have h := @MasulloRH.prime_ramp_integrated_explicit_formula
  dsimp only at h
  exact h.1 x hx

lemma tsum_norm_Kt_le (hRH : RiemannHypothesis) (x : ℝ) (hx : 1 ≤ x) :
    ∑' ρ, ‖Kt x ρ‖ ≤ βc * x ^ (-(1/2:ℝ)) := by
  have hx0 : 0 < x := by linarith
  apply (summable_Kt x hx).tsum_le_of_sum_le
  intro s
  simp_rw [norm_Kt hRH x hx0]
  rw [← Finset.mul_sum, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hL := LandauCriterion.sum_multiplicity_div_normSq_zeros_le hRH
    (s.map ⟨Subtype.val, Subtype.val_injective⟩) (by
      intro ρ hρ
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hρ
      obtain ⟨r, -, rfl⟩ := hρ
      exact ⟨r.property.1, r.property.2.1⟩)
  rw [Finset.sum_map] at hL
  simpa [βc] using hL

lemma c_nonneg (t : ℝ) (ht : 2 ≤ t) :
    0 ≤ Real.log (2*Real.pi) + (1/2) * Real.log (1 - t^(-2:ℝ)) := by
  have ht0 : 0 < t := by linarith
  have h1 : t^(-2:ℝ) ≤ 1/4 := by
    rw [Real.rpow_neg ht0.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith
  have h2 : 0 < t^(-2:ℝ) := Real.rpow_pos_of_pos ht0 _
  have h3 : Real.log (3/4) ≤ Real.log (1 - t^(-2:ℝ)) :=
    Real.log_le_log (by norm_num) (by linarith)
  have h4 : Real.log 6 ≤ Real.log (2*Real.pi) :=
    Real.log_le_log (by norm_num) (by linarith [Real.pi_gt_three])
  have h5 : Real.log (3/4) = Real.log 3 - Real.log 4 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
  have h6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h7 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  have h8 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h9 := Real.log_two_gt_d9
  nlinarith

/-- Under RH, the increments of Masullo's corrected prime ramp `M = G/x` are bounded by
`β (a^{-1/2} + b^{-1/2})`. -/
theorem M_sub_le (hRH : RiemannHypothesis) (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    Mfun b - Mfun a ≤ βc * (a ^ (-(1/2:ℝ)) + b ^ (-(1/2:ℝ))) := by
  have h := @MasulloRH.prime_ramp_integrated_explicit_formula
  dsimp only at h
  have hE := h.2 a b ha hab
  have hsa : Summable (fun ρ => Kt a ρ) := (summable_Kt a (by linarith)).of_norm
  have hsb : Summable (fun ρ => Kt b ρ) := (summable_Kt b (by linarith)).of_norm
  have hsplit : (∑' ρ : MasulloRH.ZetaZerosInTraceStrip (1/2),
      ((analyticOrderNatAt riemannZeta ρ.val : ℂ) * (b:ℂ)^(ρ.val-1)/(ρ.val*(ρ.val-1)) -
        (analyticOrderNatAt riemannZeta ρ.val : ℂ) * (a:ℂ)^(ρ.val-1)/(ρ.val*(ρ.val-1)))) =
      (∑' ρ, Kt b ρ) - ∑' ρ, Kt a ρ := (hsb.tsum_sub hsa)
  rw [hsplit] at hE
  have hint : (∫ t in a..b, ((Real.log (2*Real.pi)+(1/2)*Real.log (1-t^(-2:ℝ)):ℝ):ℂ)/(t:ℂ)^2) =
      ((∫ t in a..b, (Real.log (2*Real.pi)+(1/2)*Real.log (1-t^(-2:ℝ)))/t^2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    congr 1; funext t; push_cast; ring
  rw [hint] at hE
  have hpos : 0 ≤ ∫ t in a..b, (Real.log (2*Real.pi)+(1/2)*Real.log (1-t^(-2:ℝ)))/t^2 := by
    apply intervalIntegral.integral_nonneg hab
    intro t ht
    exact div_nonneg (c_nonneg t (by linarith [ht.1])) (by positivity)
  have hre := congrArg Complex.re hE
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hre
  have hMb : Mfun b = ((∑ n ∈ range (⌊b⌋₊+1), vonMangoldt n * max (b/(n:ℝ)-1) 0) -
      b*(Real.log b-1-Real.eulerMascheroniConstant)) / b := rfl
  have hMa : Mfun a = ((∑ n ∈ range (⌊a⌋₊+1), vonMangoldt n * max (a/(n:ℝ)-1) 0) -
      a*(Real.log a-1-Real.eulerMascheroniConstant)) / a := rfl
  have hnb : -(∑' ρ, Kt b ρ).re ≤ βc * b ^ (-(1/2:ℝ)) := by
    have := Complex.abs_re_le_norm (∑' ρ, Kt b ρ)
    have h2 := norm_tsum_le_tsum_norm (summable_Kt b (by linarith))
    have h3 := tsum_norm_Kt_le hRH b (by linarith)
    have := neg_abs_le (∑' ρ, Kt b ρ).re
    linarith
  have hna : (∑' ρ, Kt a ρ).re ≤ βc * a ^ (-(1/2:ℝ)) := by
    have := Complex.abs_re_le_norm (∑' ρ, Kt a ρ)
    have h2 := norm_tsum_le_tsum_norm (summable_Kt a (by linarith))
    have h3 := tsum_norm_Kt_le hRH a (by linarith)
    have := le_abs_self (∑' ρ, Kt a ρ).re
    linarith
  rw [hMb, hMa]

  linarith

end NicCore




namespace NicCore


noncomputable def gfun (t : ℝ) : ℝ := (Chebyshev.psi t - t) / t^2

noncomputable def Sfun (t : ℝ) : ℝ := ∑ k ∈ Ioc 0 ⌊t⌋₊, (vonMangoldt k : ℝ) / k

lemma range_sum_eq (t : ℝ) (ht : 1 ≤ t) :
    (∑ n ∈ range (⌊t⌋₊+1), vonMangoldt n * max (t/(n:ℝ)-1) 0) =
      t * Sfun t - Chebyshev.psi t := by
  have hr : range (⌊t⌋₊+1) = Icc 0 ⌊t⌋₊ := by ext; simp
  rw [hr, ← add_sum_Ioc_eq_sum_Icc (Nat.zero_le _), Chebyshev.psi_eq_sum_Icc,
    ← add_sum_Ioc_eq_sum_Icc (Nat.zero_le _)]
  simp only [ArithmeticFunction.map_zero, zero_mul, zero_add, Sfun, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_Ioc] at hk
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk.1
  have hkt : (k:ℝ) ≤ t := le_trans (by exact_mod_cast hk.2) (Nat.floor_le (by linarith))
  have hk0 : (0:ℝ) < k := by linarith
  rw [max_eq_left]
  · field_simp
  · rw [sub_nonneg, le_div_iff₀ hk0]; linarith

lemma Mfun_eq (t : ℝ) (ht : 1 ≤ t) :
    Mfun t = Sfun t - Chebyshev.psi t / t - Real.log t + 1 + Real.eulerMascheroniConstant := by
  rw [Mfun, range_sum_eq t ht]
  have : t ≠ 0 := by positivity
  field_simp
  ring

lemma psi_intervalIntegrable (a b : ℝ) : IntervalIntegrable Chebyshev.psi volume a b :=
  Chebyshev.psi_mono.intervalIntegrable

lemma gfun_intervalIntegrable (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable gfun volume a b := by
  have h0 : ∀ t ∈ Set.uIcc a b, t ≠ 0 := by
    intro t ht
    have : 0 < t := by
      rcases Set.mem_uIcc.mp ht with h | h <;> linarith [h.1]
    exact this.ne'
  have h1 : ContinuousOn (fun t : ℝ => 1 / t^2) (Set.uIcc a b) := by
    apply ContinuousOn.div continuousOn_const (continuousOn_pow 2)
    intro t ht; exact pow_ne_zero 2 (h0 t ht)
  have h2 : ContinuousOn (fun t : ℝ => t / t^2) (Set.uIcc a b) := by
    apply ContinuousOn.div continuousOn_id (continuousOn_pow 2)
    intro t ht; exact pow_ne_zero 2 (h0 t ht)
  have := ((psi_intervalIntegrable a b).mul_continuousOn h1).sub (h2.intervalIntegrable)
  refine this.congr ?_
  intro t _
  simp only [gfun]
  ring

/-- `M` is a primitive of `(ψ(t)-t)/t²`. -/
theorem integral_gfun (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, gfun t = Mfun b - Mfun a := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  -- Abel summation with f = t⁻¹
  have hA := sum_mul_eq_sub_sub_integral_mul (fun k => (vonMangoldt k : ℝ)) ha0.le hab
    (f := fun t : ℝ => t⁻¹)
    (fun t ht => differentiableAt_inv (by linarith [ht.1]))
    (by
      have : Set.EqOn (deriv fun t : ℝ => t⁻¹) (fun t => -(t^2)⁻¹) (Set.Icc a b) := by
        intro t _; exact deriv_inv
      refine (IntegrableOn.congr_fun ?_ this.symm measurableSet_Icc)
      apply ContinuousOn.integrableOn_Icc
      apply ContinuousOn.neg
      apply ContinuousOn.inv₀ (continuousOn_pow 2)
      intro t ht; exact pow_ne_zero 2 (by linarith [ht.1]))
  simp only [← Chebyshev.psi_eq_sum_Icc] at hA
  have hderiv : ∀ t ∈ Set.Ioc a b, deriv (fun t : ℝ => t⁻¹) t * Chebyshev.psi t =
      -(Chebyshev.psi t / t^2) := by
    intro t _; rw [deriv_inv]; ring
  rw [setIntegral_congr_fun measurableSet_Ioc hderiv, integral_neg,
    ← intervalIntegral.integral_of_le hab] at hA
  have hS : Sfun b = Sfun a + ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, (vonMangoldt k : ℝ) / k := by
    rw [Sfun, Sfun, Finset.sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.floor_le_floor hab)]
  have hS' : ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, (vonMangoldt k : ℝ) / k =
      ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, ((k:ℝ))⁻¹ * (vonMangoldt k : ℝ) := by
    apply Finset.sum_congr rfl; intro k _; ring
  have hpsi_int : IntervalIntegrable (fun t => Chebyshev.psi t / t^2) volume a b := by
    have h1 : ContinuousOn (fun t : ℝ => 1 / t^2) (Set.uIcc a b) := by
      apply ContinuousOn.div continuousOn_const (continuousOn_pow 2)
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      exact pow_ne_zero 2 (by linarith [ht.1])
    refine ((psi_intervalIntegrable a b).mul_continuousOn h1).congr ?_
    intro t _; simp only; ring
  have hinv_int : IntervalIntegrable (fun t : ℝ => t / t^2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_id (continuousOn_pow 2)
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact pow_ne_zero 2 (by linarith [ht.1])
  have hsplit : ∫ t in a..b, gfun t = (∫ t in a..b, Chebyshev.psi t / t^2) -
      ∫ t in a..b, t / t^2 := by
    rw [← intervalIntegral.integral_sub hpsi_int hinv_int]
    congr 1; funext t; simp only [gfun]; ring
  have hlog : ∫ t in a..b, t / t^2 = Real.log b - Real.log a := by
    have : ∫ t in a..b, t / t^2 = ∫ t in a..b, t⁻¹ := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      have : t ≠ 0 := by linarith [ht.1]
      simp only; field_simp
    rw [this, integral_inv (by
      rw [Set.uIcc_of_le hab]; intro h; linarith [h.1]),
      Real.log_div hb0.ne' ha0.ne']
  rw [hsplit, hlog, Mfun_eq b (by linarith), Mfun_eq a ha, hS, hS', hA]
  have e1 : b⁻¹ * Chebyshev.psi b = Chebyshev.psi b / b := by ring
  have e2 : a⁻¹ * Chebyshev.psi a = Chebyshev.psi a / a := by ring
  rw [e1, e2]
  ring

end NicCore




namespace NicCore


noncomputable def vfun (t : ℝ) : ℝ := 1 / Real.log t + 1 / (Real.log t)^2

noncomputable def vdfun (t : ℝ) : ℝ := -(1 / (t * (Real.log t)^2)) - 2 / (t * (Real.log t)^3)

lemma psi_rcont (t : ℝ) (ht : 0 ≤ t) : ContinuousWithinAt Chebyshev.psi (Set.Ioi t) t := by
  have hlt : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
  apply (continuousWithinAt_const (b := Chebyshev.psi t)).congr_of_eventuallyEq
  · filter_upwards [Ioo_mem_nhdsGT hlt] with u hu
    rw [Chebyshev.psi_eq_psi_coe_floor u, Chebyshev.psi_eq_psi_coe_floor t]
    congr 2
    rw [Nat.floor_eq_iff (by linarith [hu.1])]
    exact ⟨le_trans (Nat.floor_le ht) hu.1.le, hu.2⟩
  · rfl

lemma gfun_rcont (t : ℝ) (ht : 0 < t) : ContinuousWithinAt gfun (Set.Ioi t) t := by
  unfold gfun
  apply ContinuousWithinAt.div ((psi_rcont t ht.le).sub continuousWithinAt_id)
    (continuousWithinAt_id.pow 2) (pow_ne_zero 2 ht.ne')

lemma gfun_measurable : Measurable gfun := by
  unfold gfun
  have := Chebyshev.psi_mono.measurable
  fun_prop

lemma vfun_hasDerivAt (t : ℝ) (ht : 1 < t) : HasDerivAt vfun (vdfun t) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have h1 := Real.hasDerivAt_log ht0
  have hA := (hasDerivAt_const t (1:ℝ)).div h1 hl
  have hB := (hasDerivAt_const t (1:ℝ)).div (h1.pow 2) (pow_ne_zero 2 hl)
  have := hA.add hB
  have key : vdfun t = (0 * Real.log t - 1 * t⁻¹) / Real.log t ^ 2 +
      (0 * (Real.log t)^2 - 1 * ((2:ℕ) * Real.log t ^ (2 - 1) * t⁻¹)) / ((Real.log t)^2) ^ 2 := by
    unfold vdfun; field_simp; ring
  rw [key]
  exact this

lemma vdfun_continuousOn (a b : ℝ) (ha : 1 < a) (hab : a ≤ b) :
    ContinuousOn vdfun (Set.Icc a b) := by
  have hpos : ∀ t ∈ Set.Icc a b, 0 < t := fun t ht => by linarith [ht.1]
  have hlog : ContinuousOn Real.log (Set.Icc a b) :=
    Real.continuousOn_log.mono (fun t ht => (hpos t ht).ne')
  have hl0 : ∀ t ∈ Set.Icc a b, Real.log t ≠ 0 := fun t ht =>
    (Real.log_pos (by linarith [ht.1])).ne'
  unfold vdfun
  apply ContinuousOn.sub
  · apply ContinuousOn.neg
    apply ContinuousOn.div continuousOn_const (continuousOn_id.mul (hlog.pow 2))
    intro t ht; exact mul_ne_zero (hpos t ht).ne' (pow_ne_zero 2 (hl0 t ht))
  · apply ContinuousOn.div continuousOn_const (continuousOn_id.mul (hlog.pow 3))
    intro t ht; exact mul_ne_zero (hpos t ht).ne' (pow_ne_zero 3 (hl0 t ht))

lemma vdfun_nonpos (t : ℝ) (ht : 1 < t) : vdfun t ≤ 0 := by
  have hl := Real.log_pos ht
  have ht0 : 0 < t := by linarith
  unfold vdfun
  have h1 : 0 < 1 / (t * Real.log t ^ 2) := by positivity
  have h2 : 0 < 2 / (t * Real.log t ^ 3) := by positivity
  linarith

/-- Integration by parts: if the increments of a primitive `u` of `g` on `[x,y]` are bounded
by `B ≥ 0`, then `∫_x^y g v ≤ B v(x)` for the decreasing weight `v`. -/
theorem ibp_bound (x y : ℝ) (hx : 2 ≤ x) (hxy : x ≤ y)
    (hgi : ∀ a b : ℝ, 0 < a → 0 < b → IntervalIntegrable gfun volume a b)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ t, x ≤ t → t ≤ y → ∫ s in x..t, gfun s ≤ B) :
    ∫ t in x..y, gfun t * vfun t ≤ B * vfun x := by
  have hx0 : 0 < x := by linarith
  let u : ℝ → ℝ := fun t => ∫ s in x..t, gfun s
  have hgxy := hgi x y hx0 (by linarith)
  have hIcc : IntegrableOn gfun (Set.uIcc x y) volume := by
    rw [Set.uIcc_of_le hxy]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hxy).mp hgxy
  have hu_cont : ContinuousOn u (Set.uIcc x y) :=
    intervalIntegral.continuousOn_primitive_interval hIcc
  have hv_cont : ContinuousOn vfun (Set.uIcc x y) := by
    intro t ht
    rw [Set.uIcc_of_le hxy] at ht
    exact (vfun_hasDerivAt t (by linarith [ht.1])).continuousAt.continuousWithinAt
  have hu_der : ∀ t ∈ Set.Ioo (min x y) (max x y),
      HasDerivWithinAt u (gfun t) (Set.Ioi t) t := by
    intro t ht
    rw [min_eq_left hxy, max_eq_right hxy] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have h := intervalIntegral.integral_hasDerivWithinAt_right (hgi x t hx0 ht0)
      (s := Set.Ici t) (t := Set.Ioi t)
      (gfun_measurable.stronglyMeasurable.stronglyMeasurableAtFilter) (gfun_rcont t ht0)
    exact h.mono Set.Ioi_subset_Ici_self
  have hv_der : ∀ t ∈ Set.Ioo (min x y) (max x y),
      HasDerivWithinAt vfun (vdfun t) (Set.Ioi t) t := by
    intro t ht
    rw [min_eq_left hxy, max_eq_right hxy] at ht
    exact (vfun_hasDerivAt t (by linarith [ht.1])).hasDerivWithinAt
  have hvd_int : IntervalIntegrable vdfun volume x y :=
    (vdfun_continuousOn x y (by linarith) hxy).intervalIntegrable_of_Icc hxy
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDeriv_right
    hu_cont hv_cont hu_der hv_der hgxy hvd_int
  have hux : u x = 0 := intervalIntegral.integral_same
  rw [hux, zero_mul, sub_zero] at hparts
  have hgv : IntervalIntegrable (fun t => gfun t * vfun t) volume x y :=
    hgxy.mul_continuousOn hv_cont
  have huvd_cont : ContinuousOn (fun t => u t * vdfun t) (Set.Icc x y) := by
    apply ContinuousOn.mul
    · rw [← Set.uIcc_of_le hxy]; exact hu_cont
    · exact vdfun_continuousOn x y (by linarith) hxy
  have huvd : IntervalIntegrable (fun t => u t * vdfun t) volume x y :=
    huvd_cont.intervalIntegrable_of_Icc hxy
  rw [intervalIntegral.integral_add hgv huvd] at hparts
  -- bound ∫ u * vd from below by B * ∫ vd
  have hlow : ∫ t in x..y, B * vdfun t ≤ ∫ t in x..y, u t * vdfun t := by
    apply intervalIntegral.integral_mono_on hxy (hvd_int.const_mul B) huvd
    intro t ht
    have h1 := hB t ht.1 ht.2
    have h2 := vdfun_nonpos t (by linarith [ht.1])
    nlinarith
  have hvd_eq : ∫ t in x..y, vdfun t = vfun y - vfun x := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [Set.uIcc_of_le hxy] at ht
      exact vfun_hasDerivAt t (by linarith [ht.1])
    · exact hvd_int
  rw [intervalIntegral.integral_const_mul, hvd_eq] at hlow
  have huy : u y ≤ B := hB y hxy le_rfl
  have hvy : 0 ≤ vfun y := by
    have := Real.log_pos (show (1:ℝ) < y by linarith)
    unfold vfun; positivity
  have : u y * vfun y ≤ B * vfun y := mul_le_mul_of_nonneg_right huy hvy
  nlinarith

end NicCore




namespace NicCore



noncomputable def wfun (t : ℝ) : ℝ := (Real.log t + 1) / (t * Real.log t)^2

/-- `L(x) = ∑_{p ≤ x} -log(1-1/p)`. -/
noncomputable def Lfun (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 ⌊x⌋₊).filter Nat.Prime, -Real.log (1 - 1/(p:ℝ))

lemma primes_set_eq (y : ℝ) :
    (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime = (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨h2.two_le, by omega⟩, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩

lemma one_sub_inv_pos (p : ℕ) (hp : p.Prime) : 0 < 1 - 1/(p:ℝ) := by
  have : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  rw [sub_pos, div_lt_one (by linarith)]; linarith

lemma log_mertensProduct (y : ℝ) :
    Real.log (ArtinPrimitiveRoots.mertensProduct y) = -Lfun y := by
  rw [ArtinPrimitiveRoots.mertensProduct, primes_set_eq, Real.log_prod, Lfun,
    Finset.sum_neg_distrib, neg_neg]
  intro p hp
  exact (one_sub_inv_pos p (Finset.mem_filter.mp hp).2).ne'

lemma mertensProduct_pos (y : ℝ) : 0 < ArtinPrimitiveRoots.mertensProduct y := by
  apply Finset.prod_pos
  intro p hp
  exact one_sub_inv_pos p (Finset.mem_filter.mp hp).2

/-- Mertens: `L(y) - log log y → γ`. -/
lemma tendsto_L_sub : Tendsto (fun y => Lfun y - Real.log (Real.log y)) atTop
    (𝓝 Real.eulerMascheroniConstant) := by
  have h := ArtinPrimitiveRoots.mertens_product.log (Real.exp_pos _).ne'
  rw [Real.log_exp] at h
  have h2 := h.neg
  rw [neg_neg] at h2
  apply h2.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with y hy
  have hl : 0 < Real.log y := Real.log_pos hy
  rw [Real.log_mul (mertensProduct_pos y).ne' hl.ne', log_mertensProduct]
  ring

/-- Telescoping bound. -/
lemma tele (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) :
    ∑ n ∈ Finset.Ioc N M, 1 / ((n:ℝ) * ((n:ℝ) - 1)) = 1 / (N:ℝ) - 1 / (M:ℝ) := by
  induction M, hNM using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
    rw [Finset.sum_Ioc_succ_top (by omega), ih]
    have hM : (1:ℝ) ≤ M := by exact_mod_cast le_trans hN hNM
    have hM0 : (M:ℝ) ≠ 0 := by linarith
    have hM1 : (M:ℝ) + 1 ≠ 0 := by linarith
    push_cast
    rw [show ((M:ℝ) + 1 - 1) = M by ring]
    field_simp
    ring

lemma L_sub_le (x y : ℝ) (hx : 2 ≤ x) (hxy : x ≤ y) :
    Lfun y - Lfun x ≤ (∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime, 1/(p:ℝ)) + 1/(⌊x⌋₊:ℝ) := by
  have hfx : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hfxy : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor hxy
  have hU : Finset.Icc 2 ⌊y⌋₊ = Finset.Icc 2 ⌊x⌋₊ ∪ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ := by
    ext n; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hD : Disjoint (Finset.Icc 2 ⌊x⌋₊) (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊) := by
    rw [Finset.disjoint_left]; intro n h1 h2
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at h1 h2; omega
  have hLy : Lfun y = Lfun x + ∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime,
      -Real.log (1 - 1/(p:ℝ)) := by
    rw [Lfun, Lfun, hU, Finset.filter_union, Finset.sum_union (Finset.disjoint_filter_filter hD)]
  rw [hLy, add_sub_cancel_left]
  have hterm : ∀ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime,
      -Real.log (1 - 1/(p:ℝ)) ≤ 1/(p:ℝ) + 1/((p:ℝ) * ((p:ℝ) - 1)) := by
    intro p hp
    have hpp := (Finset.mem_filter.mp hp).2
    have h2 : (2:ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hl := Real.one_sub_inv_le_log_of_pos (one_sub_inv_pos p hpp)
    have : 1 - (1 - 1/(p:ℝ))⁻¹ = -(1/(p:ℝ) + 1/((p:ℝ) * ((p:ℝ) - 1))) := by
      have : (p:ℝ) - 1 ≠ 0 := by linarith
      field_simp
      ring
    linarith
  calc _ ≤ ∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime,
        (1/(p:ℝ) + 1/((p:ℝ) * ((p:ℝ) - 1))) := Finset.sum_le_sum hterm
    _ = (∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime, 1/(p:ℝ)) +
        ∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime, 1/((p:ℝ) * ((p:ℝ) - 1)) :=
          Finset.sum_add_distrib
    _ ≤ _ := by
      gcongr
      calc _ ≤ ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, 1/((n:ℝ) * ((n:ℝ) - 1)) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            intro n hn _
            have : (1:ℝ) ≤ n := by
              have := (Finset.mem_Ioc.mp hn).1; exact_mod_cast (by omega : 1 ≤ n)
            apply div_nonneg zero_le_one
            nlinarith
        _ = 1 / (⌊x⌋₊:ℝ) - 1 / (⌊y⌋₊:ℝ) := tele _ _ (by omega) hfxy
        _ ≤ 1 / (⌊x⌋₊:ℝ) := by
            have : (0:ℝ) ≤ 1 / (⌊y⌋₊:ℝ) := by positivity
            linarith

lemma hasDerivAt_f (t : ℝ) (ht : 1 < t) :
    HasDerivAt (fun t : ℝ => (t * Real.log t)⁻¹) (-wfun t) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have h := (Real.hasDerivAt_mul_log ht0).inv (mul_ne_zero ht0 hl)
  rw [show -wfun t = -(Real.log t + 1) / (t * Real.log t)^2 by unfold wfun; ring]
  exact h

lemma wfun_continuousOn (a b : ℝ) (ha : 1 < a) :
    ContinuousOn wfun (Set.Icc a b) := by
  have hpos : ∀ t ∈ Set.Icc a b, 0 < t := fun t ht => by linarith [ht.1]
  have hlog : ContinuousOn Real.log (Set.Icc a b) :=
    Real.continuousOn_log.mono (fun t ht => (hpos t ht).ne')
  unfold wfun
  apply ContinuousOn.div (hlog.add continuousOn_const) ((continuousOn_id.mul hlog).pow 2)
  intro t ht
  exact pow_ne_zero 2 (mul_ne_zero (hpos t ht).ne' (Real.log_pos (by linarith [ht.1])).ne')

/-- Abel summation for `∑ 1/p`. -/
lemma abel_primes (x y : ℝ) (hx : 2 ≤ x) (hxy : x ≤ y) :
    (∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime, 1/(p:ℝ)) =
      Chebyshev.theta y / (y * Real.log y) - Chebyshev.theta x / (x * Real.log x) +
        ∫ t in x..y, Chebyshev.theta t * wfun t := by
  let c : ℕ → ℝ := fun k => if k.Prime then Real.log k else 0
  have hderiv : ∀ t ∈ Set.Icc x y, deriv (fun t : ℝ => (t * Real.log t)⁻¹) t = -wfun t :=
    fun t ht => (hasDerivAt_f t (by linarith [ht.1])).deriv
  have hA := sum_mul_eq_sub_sub_integral_mul c (by linarith) hxy
    (f := fun t : ℝ => (t * Real.log t)⁻¹)
    (fun t ht => (hasDerivAt_f t (by linarith [ht.1])).differentiableAt)
    (by
      refine IntegrableOn.congr_fun ?_ (fun t ht => (hderiv t ht).symm) measurableSet_Icc
      exact ((wfun_continuousOn x y (by linarith)).neg).integrableOn_Icc)
  have hθ : ∀ t : ℝ, ∑ k ∈ Icc 0 ⌊t⌋₊, c k = Chebyshev.theta t := by
    intro t; rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  simp only [hθ] at hA
  have hL : ∑ k ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, (k * Real.log k)⁻¹ * c k =
      ∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime, 1/(p:ℝ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    simp only [c]
    split_ifs with hk
    · have h2 : (1:ℝ) < k := by exact_mod_cast hk.one_lt
      have hl : Real.log k ≠ 0 := (Real.log_pos h2).ne'
      field_simp
    · simp
  rw [hL] at hA
  rw [hA]
  have hI : ∫ t in Set.Ioc x y, deriv (fun t : ℝ => (t * Real.log t)⁻¹) t * Chebyshev.theta t =
      -∫ t in x..y, Chebyshev.theta t * wfun t := by
    rw [intervalIntegral.integral_of_le hxy, ← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    show deriv (fun t : ℝ => (t * Real.log t)⁻¹) t * Chebyshev.theta t = -(Chebyshev.theta t * wfun t)
    rw [hderiv t ⟨ht.1.le, ht.2⟩]; ring
  rw [hI]
  simp only [div_eq_inv_mul]
  ring

end NicCore

namespace NicCore

lemma theta_intervalIntegrable (a b : ℝ) : IntervalIntegrable Chebyshev.theta volume a b :=
  Chebyshev.theta_mono.intervalIntegrable


lemma wfun_uIcc (x y : ℝ) (hx : 1 < x) (hxy : x ≤ y) : ContinuousOn wfun (Set.uIcc x y) := by
  rw [Set.uIcc_of_le hxy]; exact wfun_continuousOn x y hx

lemma gv_eq (t : ℝ) (ht : 1 < t) : gfun t * vfun t = (Chebyshev.psi t - t) * wfun t := by
  have ht0 : t ≠ 0 := by linarith
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  unfold gfun vfun wfun
  field_simp

lemma int_tw (x y : ℝ) (hx : 2 ≤ x) (hxy : x ≤ y) :
    ∫ t in x..y, t * wfun t = (Real.log (Real.log y) - 1 / Real.log y) -
      (Real.log (Real.log x) - 1 / Real.log x) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    rw [Set.uIcc_of_le hxy] at ht
    have ht1 : 1 < t := by linarith [ht.1]
    have ht0 : t ≠ 0 := by linarith
    have hl : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
    have h1 := Real.hasDerivAt_log ht0
    have h2 := h1.log hl
    have h3 := (hasDerivAt_const t (1:ℝ)).div h1 hl
    have h4 := h2.sub h3
    rw [show t * wfun t = t⁻¹ / Real.log t - (0 * Real.log t - 1 * t⁻¹) / Real.log t ^ 2 by
      unfold wfun; field_simp; ring]
    exact h4
  · apply ContinuousOn.intervalIntegrable
    exact continuousOn_id.mul (wfun_uIcc x y (by linarith) hxy)

lemma int_split (x y : ℝ) (hx : 2 ≤ x) (hxy : x ≤ y) :
    ∫ t in x..y, Chebyshev.theta t * wfun t =
      (∫ t in x..y, t * wfun t) + (∫ t in x..y, gfun t * vfun t) -
        ∫ t in x..y, (Chebyshev.psi t - Chebyshev.theta t) * wfun t := by
  have hw := wfun_uIcc x y (by linarith) hxy
  have iθ := (theta_intervalIntegrable x y).mul_continuousOn hw
  have iψ := (psi_intervalIntegrable x y).mul_continuousOn hw
  have it : IntervalIntegrable (fun t => t * wfun t) volume x y :=
    (continuousOn_id.mul hw).intervalIntegrable
  have hgv : ∫ t in x..y, gfun t * vfun t = ∫ t in x..y, (Chebyshev.psi t * wfun t - t * wfun t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hxy] at ht
    simp only
    rw [gv_eq t (by linarith [ht.1])]; ring
  have hpt : ∫ t in x..y, (Chebyshev.psi t - Chebyshev.theta t) * wfun t =
      ∫ t in x..y, (Chebyshev.psi t * wfun t - Chebyshev.theta t * wfun t) := by
    congr 1; funext t; ring
  rw [hgv, hpt, intervalIntegral.integral_sub iψ it, intervalIntegral.integral_sub iψ iθ]
  ring

lemma vfun_anti (s t : ℝ) (hs : 1 < s) (hst : s ≤ t) : vfun t ≤ vfun s := by
  have hl : 0 < Real.log s := Real.log_pos hs
  have hlst : Real.log s ≤ Real.log t := Real.log_le_log (by linarith) hst
  unfold vfun
  have h1 : 1 / Real.log t ≤ 1 / Real.log s := one_div_le_one_div_of_le hl hlst
  have h2 : 1 / Real.log t ^ 2 ≤ 1 / Real.log s ^ 2 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hl.le hlst 2)
  linarith

lemma tendsto_theta_err : Tendsto (fun y => (Chebyshev.theta y - y) / (y * Real.log y)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun y => 1 / Real.log y) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  apply squeeze_zero_norm' _ hlog
  filter_upwards [eventually_gt_atTop (1:ℝ)] with y hy
  have hl := Real.log_pos hy
  have hy0 : 0 < y := by linarith
  have h1 := Chebyshev.theta_nonneg y
  have h2 := Chebyshev.theta_le_log4_mul_x hy0.le
  have h4 : Real.log 4 < 2 := by
    have := Real.log_two_lt_d9
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; push_cast; linarith
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos hy0 hl), div_le_div_iff₀ (mul_pos hy0 hl) hl]
  have : |Chebyshev.theta y - y| ≤ y := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  nlinarith

end NicCore

namespace NicCore

lemma c_le (t : ℝ) (ht : 2 ≤ t) :
    Real.log (2*Real.pi) + (1/2) * Real.log (1 - t^(-2:ℝ)) ≤ Real.log (2*Real.pi) := by
  have ht0 : 0 < t := by linarith
  have h2 : 0 < t^(-2:ℝ) := Real.rpow_pos_of_pos ht0 _
  have h1 : t^(-2:ℝ) ≤ 1/4 := by
    rw [Real.rpow_neg ht0.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith
  have : Real.log (1 - t^(-2:ℝ)) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  linarith

lemma integral_inv_sq (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, 1 / t^2 = 1/a - 1/b := by
  have key : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun t : ℝ => -(1/t)) (1/t^2) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have h1 := (hasDerivAt_inv ht0).neg
    have e1 : (-fun y : ℝ => y⁻¹) = (fun t : ℝ => -(1/t)) := by funext s; simp
    rw [e1] at h1
    rw [show (1:ℝ)/t^2 = - -(t^2)⁻¹ by rw [neg_neg, one_div]]
    exact h1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt key]
  · ring
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const (continuousOn_pow 2)
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact pow_ne_zero 2 (by linarith [ht.1])

/-- Lower bound for the increments of `M` under RH. -/
theorem M_sub_ge (hRH : RiemannHypothesis) (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    -(βc * (a ^ (-(1/2:ℝ)) + b ^ (-(1/2:ℝ))) + Real.log (2*Real.pi) * (1/a - 1/b)) ≤
      Mfun b - Mfun a := by
  have h := @MasulloRH.prime_ramp_integrated_explicit_formula
  dsimp only at h
  have hE := h.2 a b ha hab
  have hsa : Summable (fun ρ => Kt a ρ) := (summable_Kt a (by linarith)).of_norm
  have hsb : Summable (fun ρ => Kt b ρ) := (summable_Kt b (by linarith)).of_norm
  have hsplit : (∑' ρ : MasulloRH.ZetaZerosInTraceStrip (1/2),
      ((analyticOrderNatAt riemannZeta ρ.val : ℂ) * (b:ℂ)^(ρ.val-1)/(ρ.val*(ρ.val-1)) -
        (analyticOrderNatAt riemannZeta ρ.val : ℂ) * (a:ℂ)^(ρ.val-1)/(ρ.val*(ρ.val-1)))) =
      (∑' ρ, Kt b ρ) - ∑' ρ, Kt a ρ := (hsb.tsum_sub hsa)
  rw [hsplit] at hE
  have hint : (∫ t in a..b, ((Real.log (2*Real.pi)+(1/2)*Real.log (1-t^(-2:ℝ)):ℝ):ℂ)/(t:ℂ)^2) =
      ((∫ t in a..b, (Real.log (2*Real.pi)+(1/2)*Real.log (1-t^(-2:ℝ)))/t^2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    congr 1; funext t; push_cast; ring
  rw [hint] at hE
  have hle : ∫ t in a..b, (Real.log (2*Real.pi)+(1/2)*Real.log (1-t^(-2:ℝ)))/t^2 ≤
      Real.log (2*Real.pi) * (1/a - 1/b) := by
    have ha0 : 0 < a := by linarith
    have hcont : ContinuousOn (fun t : ℝ => 1 / t^2) (Set.uIcc a b) := by
      apply ContinuousOn.div continuousOn_const (continuousOn_pow 2)
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      exact pow_ne_zero 2 (by linarith [ht.1])
    rw [← integral_inv_sq a b ha0 hab, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab
    · -- integrability of the left integrand
      have hc1 : ContinuousOn (fun t : ℝ => Real.log (2*Real.pi)+(1/2)*Real.log (1-t^(-2:ℝ)))
          (Set.uIcc a b) := by
        apply ContinuousOn.add continuousOn_const
        apply ContinuousOn.mul continuousOn_const
        apply ContinuousOn.log
        · apply ContinuousOn.sub continuousOn_const
          apply ContinuousOn.rpow_const continuousOn_id
          intro t ht; left
          rw [Set.uIcc_of_le hab] at ht; simp; linarith [ht.1]
        · intro t ht
          rw [Set.uIcc_of_le hab] at ht
          have ht2 : 2 ≤ t := by linarith [ht.1]
          have ht0 : 0 < t := by linarith
          have h1 : t^(-2:ℝ) ≤ 1/4 := by
            rw [Real.rpow_neg ht0.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
            rw [inv_le_comm₀ (by positivity) (by norm_num)]
            nlinarith
          linarith
      have := (hc1.mul hcont).intervalIntegrable (μ := volume)
      refine this.congr ?_
      intro t _; simp only [Pi.mul_apply]; ring
    · exact (continuousOn_const.mul hcont).intervalIntegrable
    · intro t ht
      have ht2 : 2 ≤ t := by linarith [ht.1]
      have := c_le t ht2
      have hp : 0 < t^2 := by positivity
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_right this (by positivity)
  have hre := congrArg Complex.re hE
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hre
  have hMb : Mfun b = ((∑ n ∈ range (⌊b⌋₊+1), vonMangoldt n * max (b/(n:ℝ)-1) 0) -
      b*(Real.log b-1-Real.eulerMascheroniConstant)) / b := rfl
  have hMa : Mfun a = ((∑ n ∈ range (⌊a⌋₊+1), vonMangoldt n * max (a/(n:ℝ)-1) 0) -
      a*(Real.log a-1-Real.eulerMascheroniConstant)) / a := rfl
  have hnb : (∑' ρ, Kt b ρ).re ≤ βc * b ^ (-(1/2:ℝ)) := by
    have := Complex.abs_re_le_norm (∑' ρ, Kt b ρ)
    have h2 := norm_tsum_le_tsum_norm (summable_Kt b (by linarith))
    have h3 := tsum_norm_Kt_le hRH b (by linarith)
    have := le_abs_self (∑' ρ, Kt b ρ).re
    linarith
  have hna : -(∑' ρ, Kt a ρ).re ≤ βc * a ^ (-(1/2:ℝ)) := by
    have := Complex.abs_re_le_norm (∑' ρ, Kt a ρ)
    have h2 := norm_tsum_le_tsum_norm (summable_Kt a (by linarith))
    have h3 := tsum_norm_Kt_le hRH a (by linarith)
    have := neg_abs_le (∑' ρ, Kt a ρ).re
    linarith
  rw [hMb, hMa]
  linarith

end NicCore

namespace NicCore

/-- Integration by parts, lower version. -/
theorem ibp_lower (x y : ℝ) (hx : 2 ≤ x) (hxy : x ≤ y)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ t, x ≤ t → t ≤ y → -B ≤ ∫ s in x..t, gfun s) :
    -B * vfun x ≤ ∫ t in x..y, gfun t * vfun t := by
  have hgi : ∀ a b : ℝ, 0 < a → 0 < b → IntervalIntegrable gfun volume a b :=
    fun a b ha hb => gfun_intervalIntegrable a b ha hb
  have hx0 : 0 < x := by linarith
  let u : ℝ → ℝ := fun t => ∫ s in x..t, gfun s
  have hgxy := hgi x y hx0 (by linarith)
  have hIcc : IntegrableOn gfun (Set.uIcc x y) volume := by
    rw [Set.uIcc_of_le hxy]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hxy).mp hgxy
  have hu_cont : ContinuousOn u (Set.uIcc x y) :=
    intervalIntegral.continuousOn_primitive_interval hIcc
  have hv_cont : ContinuousOn vfun (Set.uIcc x y) := by
    intro t ht
    rw [Set.uIcc_of_le hxy] at ht
    exact (vfun_hasDerivAt t (by linarith [ht.1])).continuousAt.continuousWithinAt
  have hu_der : ∀ t ∈ Set.Ioo (min x y) (max x y),
      HasDerivWithinAt u (gfun t) (Set.Ioi t) t := by
    intro t ht
    rw [min_eq_left hxy, max_eq_right hxy] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have h := intervalIntegral.integral_hasDerivWithinAt_right (hgi x t hx0 ht0)
      (s := Set.Ici t) (t := Set.Ioi t)
      (gfun_measurable.stronglyMeasurable.stronglyMeasurableAtFilter) (gfun_rcont t ht0)
    exact h.mono Set.Ioi_subset_Ici_self
  have hv_der : ∀ t ∈ Set.Ioo (min x y) (max x y),
      HasDerivWithinAt vfun (vdfun t) (Set.Ioi t) t := by
    intro t ht
    rw [min_eq_left hxy, max_eq_right hxy] at ht
    exact (vfun_hasDerivAt t (by linarith [ht.1])).hasDerivWithinAt
  have hvd_int : IntervalIntegrable vdfun volume x y :=
    (vdfun_continuousOn x y (by linarith) hxy).intervalIntegrable_of_Icc hxy
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDeriv_right
    hu_cont hv_cont hu_der hv_der hgxy hvd_int
  have hux : u x = 0 := intervalIntegral.integral_same
  rw [hux, zero_mul, sub_zero] at hparts
  have hgv : IntervalIntegrable (fun t => gfun t * vfun t) volume x y :=
    hgxy.mul_continuousOn hv_cont
  have huvd_cont : ContinuousOn (fun t => u t * vdfun t) (Set.Icc x y) := by
    apply ContinuousOn.mul
    · rw [← Set.uIcc_of_le hxy]; exact hu_cont
    · exact vdfun_continuousOn x y (by linarith) hxy
  have huvd : IntervalIntegrable (fun t => u t * vdfun t) volume x y :=
    huvd_cont.intervalIntegrable_of_Icc hxy
  rw [intervalIntegral.integral_add hgv huvd] at hparts
  have hup : ∫ t in x..y, u t * vdfun t ≤ ∫ t in x..y, (-B) * vdfun t := by
    apply intervalIntegral.integral_mono_on hxy huvd (hvd_int.const_mul (-B))
    intro t ht
    have h1 := hB t ht.1 ht.2
    have h2 := vdfun_nonpos t (by linarith [ht.1])
    nlinarith
  have hvd_eq : ∫ t in x..y, vdfun t = vfun y - vfun x := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [Set.uIcc_of_le hxy] at ht
      exact vfun_hasDerivAt t (by linarith [ht.1])
    · exact hvd_int
  rw [intervalIntegral.integral_const_mul, hvd_eq] at hup
  have huy : -B ≤ u y := hB y hxy le_rfl
  have hvy : 0 ≤ vfun y := by
    have := Real.log_pos (show (1:ℝ) < y by linarith)
    unfold vfun; positivity
  have : -B * vfun y ≤ u y * vfun y := mul_le_mul_of_nonneg_right huy hvy
  nlinarith

lemma L_sub_ge (x y : ℝ) (hx : 2 ≤ x) (hxy : x ≤ y) :
    (∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime, 1/(p:ℝ)) ≤ Lfun y - Lfun x := by
  have hfx : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hfxy : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor hxy
  have hU : Finset.Icc 2 ⌊y⌋₊ = Finset.Icc 2 ⌊x⌋₊ ∪ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ := by
    ext n; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hD : Disjoint (Finset.Icc 2 ⌊x⌋₊) (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊) := by
    rw [Finset.disjoint_left]; intro n h1 h2
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at h1 h2; omega
  have hLy : Lfun y = Lfun x + ∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime,
      -Real.log (1 - 1/(p:ℝ)) := by
    rw [Lfun, Lfun, hU, Finset.filter_union, Finset.sum_union (Finset.disjoint_filter_filter hD)]
  rw [hLy, add_sub_cancel_left]
  apply Finset.sum_le_sum
  intro p hp
  have hpp := (Finset.mem_filter.mp hp).2
  have h0 := one_sub_inv_pos p hpp
  have hl := Real.log_le_sub_one_of_pos h0
  linarith

end NicCore

namespace NicCore

noncomputable def Fk (α b s : ℝ) : ℝ := s^(-α) / α * (1 / Real.log s - b / (Real.log s)^2)

noncomputable def gk (α b s : ℝ) : ℝ :=
  s^(-α) / s * (1 / Real.log s + (1/α - b) / (Real.log s)^2 - (2*b/α) / (Real.log s)^3)

lemma Fk_hasDerivAt (α b s : ℝ) (hα : 0 < α) (hs : 1 < s) :
    HasDerivAt (Fk α b) (-gk α b s) s := by
  have hs0 : s ≠ 0 := by linarith
  have hl : Real.log s ≠ 0 := (Real.log_pos hs).ne'
  have h1 : HasDerivAt (fun x : ℝ => x^(-α)) (-α * s^(-α-1)) s :=
    Real.hasDerivAt_rpow_const (Or.inl hs0)
  have hL := Real.hasDerivAt_log hs0
  have h2 := ((hasDerivAt_const s (1:ℝ)).div hL hl).sub
    ((hasDerivAt_const s b).div (hL.pow 2) (pow_ne_zero 2 hl))
  have h3 := (h1.div_const α).mul h2
  have e : Fk α b = (fun x : ℝ => x^(-α)/α) * ((fun _ => (1:ℝ))/Real.log - (fun _ => b)/Real.log^2) := by
    funext x; simp only [Fk, Pi.mul_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply]
  rw [e]
  refine h3.congr_deriv ?_
  simp only [Pi.sub_apply, Pi.div_apply, Pi.pow_apply]
  rw [Real.rpow_sub_one hs0]
  unfold gk
  field_simp
  ring

lemma gk_continuousOn (α b t y : ℝ) (ht : 1 < t) :
    ContinuousOn (gk α b) (Set.Icc t y) := by
  have hpos : ∀ s ∈ Set.Icc t y, 0 < s := fun s hs => by linarith [hs.1]
  have hlog : ContinuousOn Real.log (Set.Icc t y) :=
    Real.continuousOn_log.mono (fun s hs => (hpos s hs).ne')
  have hl0 : ∀ s ∈ Set.Icc t y, Real.log s ≠ 0 := fun s hs =>
    (Real.log_pos (by linarith [hs.1])).ne'
  unfold gk
  apply ContinuousOn.mul
  · apply ContinuousOn.div _ continuousOn_id (fun s hs => (hpos s hs).ne')
    exact ContinuousOn.rpow_const continuousOn_id (fun s hs => Or.inl (hpos s hs).ne')
  · apply ContinuousOn.sub
    · apply ContinuousOn.add
      · exact continuousOn_const.div hlog hl0
      · exact continuousOn_const.div (hlog.pow 2) (fun s hs => pow_ne_zero 2 (hl0 s hs))
    · exact continuousOn_const.div (hlog.pow 3) (fun s hs => pow_ne_zero 3 (hl0 s hs))

lemma rpow_w_le (α b L0 s : ℝ) (hα : 0 < α) (hb : 0 ≤ b) (hL0 : 0 < L0)
    (hcond : 2*b/α ≤ (1/α - b - 1) * L0) (hs : 1 < s) (hLs : L0 ≤ Real.log s) :
    s^(1-α) * wfun s ≤ gk α b s := by
  have hs0 : 0 < s := by linarith
  have hl : 0 < Real.log s := Real.log_pos hs
  have hP : 0 < s^(-α) := Real.rpow_pos_of_pos hs0 _
  have e1 : s^(1-α) = s * s^(-α) := by
    rw [show (1:ℝ) - α = 1 + (-α) by ring, Real.rpow_add hs0, Real.rpow_one]
  have hk : 0 ≤ 1/α - b - 1 := by
    by_contra h; push_neg at h
    have : (1/α - b - 1) * L0 < 0 := mul_neg_of_neg_of_pos h hL0
    have : 0 ≤ 2*b/α := by positivity
    linarith
  have hc2 : 2*b/α ≤ (1/α - b - 1) * Real.log s :=
    le_trans hcond (mul_le_mul_of_nonneg_left hLs hk)
  rw [e1]; unfold wfun gk
  have key : 1 / Real.log s^2 ≤ (1/α - b) / Real.log s^2 - (2*b/α) / Real.log s^3 := by
    rw [div_sub_div _ _ (by positivity) (by positivity), le_div_iff₀ (by positivity)]
    have : (2*b/α) * Real.log s^2 ≤ ((1/α - b - 1) * Real.log s) * Real.log s^2 :=
      mul_le_mul_of_nonneg_right hc2 (by positivity)
    have e3 : 1 / Real.log s^2 * (Real.log s^2 * Real.log s^3) = Real.log s^3 := by
      field_simp
    rw [e3]
    nlinarith [pow_pos hl 2, pow_pos hl 3, pow_pos hl 5]
  have : s * s^(-α) * ((Real.log s + 1) / (s * Real.log s)^2) =
      s^(-α) / s * (1 / Real.log s + 1 / Real.log s^2) := by
    field_simp
  rw [this]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith

theorem int_rpow_w (α b L0 t y : ℝ) (hα : 0 < α) (hb : 0 ≤ b) (hL0 : 0 < L0) (hbL : b ≤ L0)
    (hcond : 2*b/α ≤ (1/α - b - 1) * L0) (ht : 1 < t) (hLt : L0 ≤ Real.log t) (hty : t ≤ y) :
    ∫ s in t..y, s^(1-α) * wfun s ≤ Fk α b t := by
  have hgi : IntervalIntegrable (gk α b) volume t y :=
    (gk_continuousOn α b t y ht).intervalIntegrable_of_Icc hty
  have hfi : IntervalIntegrable (fun s => s^(1-α) * wfun s) volume t y := by
    apply ContinuousOn.intervalIntegrable_of_Icc hty
    apply ContinuousOn.mul
    · exact ContinuousOn.rpow_const continuousOn_id (fun s hs => Or.inl (by linarith [hs.1]))
    · exact wfun_continuousOn t y ht
  have hmono : ∫ s in t..y, s^(1-α) * wfun s ≤ ∫ s in t..y, gk α b s := by
    apply intervalIntegral.integral_mono_on hty hfi hgi
    intro s hs
    have hs1 : 1 < s := by linarith [hs.1]
    have hLs : L0 ≤ Real.log s := le_trans hLt (Real.log_le_log (by linarith) hs.1)
    exact rpow_w_le α b L0 s hα hb hL0 hcond hs1 hLs
  have hFTC : ∫ s in t..y, gk α b s = Fk α b t - Fk α b y := by
    have : ∫ s in t..y, gk α b s = -∫ s in t..y, -gk α b s := by
      rw [intervalIntegral.integral_neg, neg_neg]
    rw [this, intervalIntegral.integral_eq_sub_of_hasDerivAt (f := Fk α b)]
    · ring
    · intro s hs
      rw [Set.uIcc_of_le hty] at hs
      exact Fk_hasDerivAt α b s hα (by linarith [hs.1])
    · exact hgi.neg
  have hFy : 0 ≤ Fk α b y := by
    have hy1 : 1 < y := by linarith
    have hly : L0 ≤ Real.log y := le_trans hLt (Real.log_le_log (by linarith) hty)
    have hl : 0 < Real.log y := by linarith
    unfold Fk
    apply mul_nonneg (div_nonneg (Real.rpow_nonneg (by linarith) _) hα.le)
    rw [div_sub_div _ _ hl.ne' (by positivity)]
    apply div_nonneg _ (by positivity)
    nlinarith
  linarith

end NicCore

namespace NicCore

noncomputable def E1 (t : ℝ) : ℝ := (2 * βc * t^(-(1/2:ℝ)) + Real.log (2*Real.pi) / t) * vfun t

noncomputable def E2 (t : ℝ) : ℝ :=
  1.04 * (Fk (1/2) (3/5) t + Fk (2/3) (1/3) t + Fk (4/5) (1/6) t)

lemma log_ge_six (t : ℝ) (ht : 1000 ≤ t) : 6 ≤ Real.log t := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have h := Real.exp_one_lt_d9
  have : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  have h0 := Real.exp_pos 1
  calc Real.exp 1 ^ 6 ≤ (2.7182818286:ℝ)^6 := pow_le_pow_left₀ h0.le h.le 6
    _ ≤ 1000 := by norm_num
    _ ≤ t := ht

lemma psi_theta_int (t y : ℝ) (ht : 1000 ≤ t) (hty : t ≤ y) :
    ∫ s in t..y, (Chebyshev.psi s - Chebyshev.theta s) * wfun s ≤ E2 t := by
  have ht1 : 1 < t := by linarith
  have hw := wfun_continuousOn t y ht1
  have hr : ∀ α : ℝ, ContinuousOn (fun s : ℝ => s^(1-α) * wfun s) (Set.Icc t y) := fun α =>
    (ContinuousOn.rpow_const continuousOn_id (fun s hs => Or.inl (by simp only [id]; linarith [hs.1]))).mul hw
  have hi : ∀ α : ℝ, IntervalIntegrable (fun s : ℝ => s^(1-α) * wfun s) volume t y :=
    fun α => (hr α).intervalIntegrable_of_Icc hty
  have iψθ : IntervalIntegrable (fun s => (Chebyshev.psi s - Chebyshev.theta s) * wfun s) volume t y :=
    ((psi_intervalIntegrable t y).sub (theta_intervalIntegrable t y)).mul_continuousOn
      (by rw [Set.uIcc_of_le hty]; exact hw)
  have hmono : ∫ s in t..y, (Chebyshev.psi s - Chebyshev.theta s) * wfun s ≤
      ∫ s in t..y, 1.04 * ((s^(1-(1/2:ℝ)) * wfun s + s^(1-(2/3:ℝ)) * wfun s) + s^(1-(4/5:ℝ)) * wfun s) := by
    apply intervalIntegral.integral_mono_on hty iψθ
    · exact (((hi _).add (hi _)).add (hi _)).const_mul _
    · intro s hs
      have hs0 : 0 < s := by linarith [hs.1]
      have hws : 0 ≤ wfun s := by
        unfold wfun; have := Real.log_pos (show (1:ℝ) < s by linarith [hs.1]); positivity
      have h1 := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi s
      have p2 := TaoFivePrimes.rosser_schoenfeld_psi_le (s ^ (2:ℝ)⁻¹) (Real.rpow_pos_of_pos hs0 _)
      have p3 := TaoFivePrimes.rosser_schoenfeld_psi_le (s ^ (3:ℝ)⁻¹) (Real.rpow_pos_of_pos hs0 _)
      have p5 := TaoFivePrimes.rosser_schoenfeld_psi_le (s ^ (5:ℝ)⁻¹) (Real.rpow_pos_of_pos hs0 _)
      have e2 : (1:ℝ) - 1/2 = (2:ℝ)⁻¹ := by norm_num
      have e3 : (1:ℝ) - 2/3 = (3:ℝ)⁻¹ := by norm_num
      have e5 : (1:ℝ) - 4/5 = (5:ℝ)⁻¹ := by norm_num
      rw [e2, e3, e5]
      have : (Chebyshev.psi s - Chebyshev.theta s) ≤
          1.04 * (s ^ (2:ℝ)⁻¹ + s ^ (3:ℝ)⁻¹ + s ^ (5:ℝ)⁻¹) := by linarith
      calc (Chebyshev.psi s - Chebyshev.theta s) * wfun s ≤
            1.04 * (s ^ (2:ℝ)⁻¹ + s ^ (3:ℝ)⁻¹ + s ^ (5:ℝ)⁻¹) * wfun s :=
              mul_le_mul_of_nonneg_right this hws
        _ = _ := by ring
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add ((hi _).add (hi _)) (hi _),
    intervalIntegral.integral_add (hi _) (hi _)] at hmono
  have hL := log_ge_six t ht
  have k2 := int_rpow_w (1/2) (3/5) 6 t y (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ht1 hL hty
  have k3 := int_rpow_w (2/3) (1/3) 6 t y (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ht1 hL hty
  have k5 := int_rpow_w (4/5) (1/6) 6 t y (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ht1 hL hty
  unfold E2
  nlinarith

lemma beta_nonneg (hRH : RiemannHypothesis) : 0 ≤ βc := by
  have := LandauCriterion.sum_multiplicity_div_normSq_zeros_le hRH ∅ (by simp)
  simpa [βc] using this

/-- Upper Mertens bound under RH. -/
theorem L_upper (hRH : RiemannHypothesis) (t : ℝ) (ht : 1000 ≤ t) :
    Lfun t ≤ Real.eulerMascheroniConstant + Real.log (Real.log t) +
      (Chebyshev.theta t - t) / (t * Real.log t) + E1 t + E2 t := by
  have ht2 : 2 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hβ := beta_nonneg hRH
  set B := 2 * βc * t^(-(1/2:ℝ)) + Real.log (2*Real.pi) / t with hBdef
  have hl2π : 0 ≤ Real.log (2*Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hB0 : 0 ≤ B := by
    have : 0 ≤ t^(-(1/2:ℝ)) := Real.rpow_nonneg ht0.le _
    positivity
  have hgv : ∀ y, t ≤ y → -B * vfun t ≤ ∫ s in t..y, gfun s * vfun s := by
    intro y hty
    apply ibp_lower t y ht2 hty B hB0
    intro s hts hsy
    rw [integral_gfun t s (by linarith) hts]
    have hM := M_sub_ge hRH t s ht2 hts
    have h1 : s^(-(1/2:ℝ)) ≤ t^(-(1/2:ℝ)) := Real.rpow_le_rpow_of_nonpos ht0 hts (by norm_num)
    have h2 : 0 ≤ 1/s := by have : 0 < s := by linarith
                            positivity
    have h3 : βc * s^(-(1/2:ℝ)) ≤ βc * t^(-(1/2:ℝ)) := mul_le_mul_of_nonneg_left h1 hβ
    have h4 : Real.log (2*Real.pi) * (1/t - 1/s) ≤ Real.log (2*Real.pi) / t := by
      have : Real.log (2*Real.pi) * (1/s) ≥ 0 := mul_nonneg hl2π h2
      rw [mul_sub]; rw [mul_one_div]; linarith
    rw [hBdef]; linarith
  set C := Lfun t - Real.log (Real.log t) - (Chebyshev.theta t - t) / (t * Real.log t) - E1 t - E2 t
  have hy : ∀ y, t ≤ y → C ≤ (Lfun y - Real.log (Real.log y)) -
      (Chebyshev.theta y - y) / (y * Real.log y) := by
    intro y hty
    have h1 := L_sub_ge t y ht2 hty
    have h2 := abel_primes t y ht2 hty
    have h3 := int_split t y ht2 hty
    have h4 := int_tw t y ht2 hty
    have h5 := hgv y hty
    have h6 := psi_theta_int t y ht hty
    have hy1 : 0 < Real.log y := Real.log_pos (by linarith)
    have hy0 : 0 < y := by linarith
    have ht1 : 0 < Real.log t := Real.log_pos (by linarith)
    have e : Chebyshev.theta y / (y * Real.log y) - 1 / Real.log y =
        (Chebyshev.theta y - y) / (y * Real.log y) := by
      field_simp
    have e' : Chebyshev.theta t / (t * Real.log t) - 1 / Real.log t =
        (Chebyshev.theta t - t) / (t * Real.log t) := by
      field_simp
    have hE1 : E1 t = B * vfun t := rfl
    simp only [C]
    linarith
  have hlim := (tendsto_L_sub.sub tendsto_theta_err)
  rw [sub_zero] at hlim
  have hγ : C ≤ Real.eulerMascheroniConstant := by
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop t] with y hy'
    exact hy y hy'
  simp only [C] at hγ
  linarith

end NicCore

-- ===== Abel =====

set_option autoImplicit false
open Finset MeasureTheory Filter Topology

namespace NicCore

noncomputable def fq (u : ℝ) : ℝ := 1 / (u^2 * Real.log u)
noncomputable def wq (u : ℝ) : ℝ := (2 * Real.log u + 1) / (u^3 * (Real.log u)^2)

lemma fq_hasDerivAt (u : ℝ) (hu : 1 < u) : HasDerivAt fq (-wq u) u := by
  have hu0 : u ≠ 0 := by linarith
  have hl : Real.log u ≠ 0 := (Real.log_pos hu).ne'
  have h := ((hasDerivAt_pow 2 u).mul (Real.hasDerivAt_log hu0)).inv
    (mul_ne_zero (pow_ne_zero 2 hu0) hl)
  have e : fq = fun u : ℝ => (u^2 * Real.log u)⁻¹ := by funext x; simp [fq]
  rw [e]
  have e2 : ((fun x : ℝ => x ^ 2) * Real.log)⁻¹ = fun u : ℝ => (u^2 * Real.log u)⁻¹ := by
    funext x; simp
  rw [e2] at h
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  unfold wq
  field_simp
  ring

lemma wq_continuousOn (a b : ℝ) (ha : 1 < a) : ContinuousOn wq (Set.Icc a b) := by
  have hpos : ∀ t ∈ Set.Icc a b, 0 < t := fun t ht => by linarith [ht.1]
  have hlog : ContinuousOn Real.log (Set.Icc a b) :=
    Real.continuousOn_log.mono (fun t ht => (hpos t ht).ne')
  unfold wq
  apply ContinuousOn.div ((continuousOn_const.mul hlog).add continuousOn_const)
    ((continuousOn_pow 3).mul (hlog.pow 2))
  intro t ht
  exact mul_ne_zero (pow_ne_zero 3 (hpos t ht).ne') (pow_ne_zero 2 (Real.log_pos (by linarith [ht.1])).ne')

lemma fq_continuousOn (a b : ℝ) (ha : 1 < a) : ContinuousOn fq (Set.Icc a b) := by
  have hpos : ∀ t ∈ Set.Icc a b, 0 < t := fun t ht => by linarith [ht.1]
  have hlog : ContinuousOn Real.log (Set.Icc a b) :=
    Real.continuousOn_log.mono (fun t ht => (hpos t ht).ne')
  unfold fq
  apply ContinuousOn.div continuousOn_const ((continuousOn_pow 2).mul hlog)
  intro t ht
  exact mul_ne_zero (pow_ne_zero 2 (hpos t ht).ne') (Real.log_pos (by linarith [ht.1])).ne'

/-- Abel summation for `∑ 1/p²`. -/
lemma abel_inv_sq (x y : ℝ) (hx : 2 ≤ x) (hxy : x ≤ y) :
    (∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime, 1/(p:ℝ)^2) =
      fq y * Chebyshev.theta y - fq x * Chebyshev.theta x +
        ∫ t in x..y, Chebyshev.theta t * wq t := by
  let c : ℕ → ℝ := fun k => if k.Prime then Real.log k else 0
  have hderiv : ∀ t ∈ Set.Icc x y, deriv fq t = -wq t :=
    fun t ht => (fq_hasDerivAt t (by linarith [ht.1])).deriv
  have hA := sum_mul_eq_sub_sub_integral_mul c (by linarith) hxy
    (f := fq)
    (fun t ht => (fq_hasDerivAt t (by linarith [ht.1])).differentiableAt)
    (by
      refine IntegrableOn.congr_fun ?_ (fun t ht => (hderiv t ht).symm) measurableSet_Icc
      exact ((wq_continuousOn x y (by linarith)).neg).integrableOn_Icc)
  have hθ : ∀ t : ℝ, ∑ k ∈ Icc 0 ⌊t⌋₊, c k = Chebyshev.theta t := by
    intro t; rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  simp only [hθ] at hA
  have hL : ∑ k ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, fq k * c k =
      ∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime, 1/(p:ℝ)^2 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    simp only [c]
    split_ifs with hk
    · have h2 : (1:ℝ) < k := by exact_mod_cast hk.one_lt
      have hl : Real.log k ≠ 0 := (Real.log_pos h2).ne'
      unfold fq
      field_simp
    · simp
  rw [hL] at hA
  rw [hA]
  have hI : ∫ t in Set.Ioc x y, deriv fq t * Chebyshev.theta t =
      -∫ t in x..y, Chebyshev.theta t * wq t := by
    rw [intervalIntegral.integral_of_le hxy, ← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    show deriv fq t * Chebyshev.theta t = -(Chebyshev.theta t * wq t)
    rw [hderiv t ⟨ht.1.le, ht.2⟩]; ring
  rw [hI]
  ring

/-- Lower bound for `∑_{Y<p≤t} 1/p²` from a lower bound `ℓ ≤ θ` on `[Y,t]`. -/
theorem sum_inv_sq_lower (Y t : ℝ) (hY : 2 ≤ Y) (hYt : Y ≤ t)
    (ℓ ℓ' : ℝ → ℝ) (hℓ : ∀ u ∈ Set.Icc Y t, ℓ u ≤ Chebyshev.theta u)
    (hd : ∀ u ∈ Set.Icc Y t, HasDerivAt ℓ (ℓ' u) u)
    (hc : ContinuousOn ℓ' (Set.Icc Y t))
    (m : ℝ) (hm0 : 0 ≤ m) (hm : ∀ u ∈ Set.Icc Y t, m ≤ ℓ' u) :
    fq Y * (ℓ Y - Chebyshev.theta Y) +
        m / (1 + 1 / Real.log Y) * ((Y * Real.log Y)⁻¹ - (t * Real.log t)⁻¹) ≤
      ∑ p ∈ (Finset.Ioc ⌊Y⌋₊ ⌊t⌋₊).filter Nat.Prime, 1/(p:ℝ)^2 := by
  have hY1 : 1 < Y := by linarith
  rw [abel_inv_sq Y t hY hYt]
  have hwc := wq_continuousOn Y t hY1
  have hfc := fq_continuousOn Y t hY1
  have hℓc : ContinuousOn ℓ (Set.Icc Y t) := fun u hu => (hd u hu).continuousAt.continuousWithinAt
  have hwnn : ∀ u, 1 < u → 0 ≤ wq u := by
    intro u hu; unfold wq; have := Real.log_pos hu; positivity
  have hfnn : ∀ u, 1 < u → 0 ≤ fq u := by
    intro u hu; unfold fq; have := Real.log_pos hu; positivity
  -- ∫ θ w ≥ ∫ ℓ w
  have h1 : ∫ u in Y..t, ℓ u * wq u ≤ ∫ u in Y..t, Chebyshev.theta u * wq u := by
    apply intervalIntegral.integral_mono_on hYt
    · exact (hℓc.mul hwc).intervalIntegrable_of_Icc hYt
    · exact (theta_intervalIntegrable Y t).mul_continuousOn (by rw [Set.uIcc_of_le hYt]; exact hwc)
    · intro u hu
      exact mul_le_mul_of_nonneg_right (hℓ u hu) (hwnn u (by linarith [hu.1]))
  have h2 : fq t * ℓ t ≤ fq t * Chebyshev.theta t :=
    mul_le_mul_of_nonneg_left (hℓ t ⟨hYt, le_rfl⟩) (hfnn t (by linarith))
  -- integration by parts: ∫ ℓ (-wq) = ℓ t fq t - ℓ Y fq Y - ∫ ℓ' fq
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := ℓ) (v := fq) (u' := ℓ') (v' := fun u => -wq u) (a := Y) (b := t)
    (by rw [Set.uIcc_of_le hYt]; exact hℓc)
    (by rw [Set.uIcc_of_le hYt]; exact hfc)
    (by intro u hu; simp only [min_eq_left hYt, max_eq_right hYt] at hu
        exact hd u ⟨hu.1.le, hu.2.le⟩)
    (by intro u hu; simp only [min_eq_left hYt, max_eq_right hYt] at hu
        exact fq_hasDerivAt u (by linarith [hu.1]))
    (hc.intervalIntegrable_of_Icc hYt)
    (hwc.neg.intervalIntegrable_of_Icc hYt)
  have hneg : ∫ u in Y..t, ℓ u * -wq u = -∫ u in Y..t, ℓ u * wq u := by
    rw [← intervalIntegral.integral_neg]; congr 1; funext u; ring
  rw [hneg] at hparts
  -- ∫ ℓ' fq ≥ m ∫ fq ≥ m/(1+1/log Y) ∫ wfun
  have hwf : ∀ u, 1 < u → wfun u = (1 + 1 / Real.log u) * fq u := by
    intro u hu
    have hl : Real.log u ≠ 0 := (Real.log_pos hu).ne'
    have hu0 : u ≠ 0 := by linarith
    unfold wfun fq; field_simp
  have hlY : 0 < Real.log Y := Real.log_pos hY1
  have h3 : ∫ u in Y..t, m / (1 + 1 / Real.log Y) * wfun u ≤ ∫ u in Y..t, ℓ' u * fq u := by
    apply intervalIntegral.integral_mono_on hYt
    · exact (continuousOn_const.mul (wfun_continuousOn Y t hY1)).intervalIntegrable_of_Icc hYt
    · exact (hc.mul hfc).intervalIntegrable_of_Icc hYt
    · intro u hu
      have hu1 : 1 < u := by linarith [hu.1]
      have hlu : Real.log Y ≤ Real.log u := Real.log_le_log (by linarith) hu.1
      have hlu0 : 0 < Real.log u := Real.log_pos hu1
      rw [hwf u hu1]
      have hk : 1 + 1 / Real.log u ≤ 1 + 1 / Real.log Y := by
        have := one_div_le_one_div_of_le hlY hlu; linarith
      have hf0 := hfnn u hu1
      have hpos : 0 < 1 + 1 / Real.log Y := by positivity
      calc m / (1 + 1 / Real.log Y) * ((1 + 1 / Real.log u) * fq u)
          ≤ m / (1 + 1 / Real.log Y) * ((1 + 1 / Real.log Y) * fq u) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_right hk hf0
        _ = m * fq u := by field_simp
        _ ≤ ℓ' u * fq u := mul_le_mul_of_nonneg_right (hm u hu) hf0
  have hwint : ∫ u in Y..t, wfun u = (Y * Real.log Y)⁻¹ - (t * Real.log t)⁻¹ := by
    have : ∫ u in Y..t, -wfun u = (t * Real.log t)⁻¹ - (Y * Real.log Y)⁻¹ := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro u hu
        rw [Set.uIcc_of_le hYt] at hu
        exact hasDerivAt_f u (by linarith [hu.1])
      · exact (wfun_continuousOn Y t hY1).neg.intervalIntegrable_of_Icc hYt
    rw [intervalIntegral.integral_neg] at this
    linarith
  rw [intervalIntegral.integral_const_mul, hwint] at h3
  nlinarith

end NicCore

-- ===== Combine =====

set_option autoImplicit false
open Finset

namespace RobinRH
open NicCore

lemma eps_le (t : ℝ) (ht : 1 < t) : eps t ≤ 1 / (t * Real.log t) := by
  have hl0 := Real.log_pos ht
  have ht0 : 0 < t := by linarith
  unfold eps
  rw [div_le_div_iff₀ hl0 (by positivity)]
  have := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < 1 + 1/t)
  have : Real.log (1 + 1/t) * (t * Real.log t) ≤ (1/t) * (t * Real.log t) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  rw [show (1/t) * (t * Real.log t) = Real.log t by field_simp] at this
  linarith

lemma eps_ge (t : ℝ) (ht : 1 < t) : 1 / ((t+1) * Real.log t) ≤ eps t := by
  have hl0 := Real.log_pos ht
  have ht0 : 0 < t := by linarith
  unfold eps
  rw [div_le_div_iff₀ (by positivity) hl0]
  have := Real.one_sub_inv_le_log_of_pos (by positivity : (0:ℝ) < 1 + 1/t)
  have e : 1 - (1 + 1/t)⁻¹ = 1 / (t+1) := by field_simp; ring
  rw [e] at this
  have : 1 / (t+1) * ((t+1) * Real.log t) ≤ Real.log (1 + 1/t) * ((t+1) * Real.log t) :=
    mul_le_mul_of_nonneg_right this (by positivity)
  rw [show 1 / (t+1) * ((t+1) * Real.log t) = Real.log t by field_simp] at this
  linarith

lemma cross_term (t : ℝ) (ht : 2 ≤ t) :
    eps t * (t - Chebyshev.theta t) + (Chebyshev.theta t - t) / (t * Real.log t)
      ≤ 0.04 / (t * Real.log t) := by
  have ht1 : 1 < t := by linarith
  have hl0 := Real.log_pos ht1
  have ht0 : 0 < t := by linarith
  have h1 := eps_le t ht1
  have h2 := eps_ge t ht1
  have hth : Chebyshev.theta t ≤ 1.04 * t :=
    (Chebyshev.theta_le_psi t).trans (TaoFivePrimes.rosser_schoenfeld_psi_le t ht0)
  have e : eps t * (t - Chebyshev.theta t) + (Chebyshev.theta t - t) / (t * Real.log t)
      = (Chebyshev.theta t - t) * (1 / (t * Real.log t) - eps t) := by ring
  rw [e]
  have hpos : 0 < 0.04 / (t * Real.log t) := by positivity
  rcases le_total (Chebyshev.theta t) t with h | h
  · have : (Chebyshev.theta t - t) * (1 / (t * Real.log t) - eps t) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    linarith
  · have h3 : 1 / (t * Real.log t) - eps t ≤ 1 / (t * Real.log t) - 1 / ((t+1) * Real.log t) := by
      linarith
    have h4 : 1 / (t * Real.log t) - 1 / ((t+1) * Real.log t) = 1 / (t * (t+1) * Real.log t) := by
      field_simp; ring
    have h5 : (Chebyshev.theta t - t) * (1 / (t * Real.log t) - eps t)
        ≤ (0.04 * t) * (1 / (t * (t+1) * Real.log t)) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
    have h6 : (0.04 * t) * (1 / (t * (t+1) * Real.log t)) ≤ 0.04 / (t * Real.log t) := by
      rw [show (0.04 * t) * (1 / (t * (t+1) * Real.log t)) = 0.04 / ((t+1) * Real.log t) by
        field_simp]
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul_of_nonneg_right (by linarith) hl0.le)
    linarith

/-- Robin's inequality for `n` with `log n ≥ 1000`, given the gap inequality at `t = log n`. -/
theorem robin_of_gap (hRH : RiemannHypothesis) (J n : ℕ) (ht : 1000 ≤ Real.log n)
    (hgap : E1 (Real.log n) + E2 (Real.log n) + 0.04 / (Real.log n * Real.log (Real.log n))
      < Gf J (Real.log n)) :
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) <
      Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by
  set t := Real.log n with htdef
  have hn0 : (0:ℝ) < n := by
    by_contra h; push_neg at h
    have : (n:ℝ) = 0 := le_antisymm h (Nat.cast_nonneg n)
    rw [htdef, this, Real.log_zero] at ht; linarith
  have hn3 : 3 ≤ n := by
    by_contra h; push_neg at h
    have : (n:ℝ) ≤ 2 := by exact_mod_cast (by omega : n ≤ 2)
    have := Real.log_le_sub_one_of_pos hn0
    linarith
  have hloc := local_bound J n hn3
  have hL := L_upper hRH t ht
  have hc := cross_term t (by linarith)
  have hLf : Lf t = Lfun t := rfl
  rw [← htdef, hLf] at hloc
  have hlt : 0 < Real.log t := Real.log_pos (by linarith)
  have key : Real.log ((ArithmeticFunction.sigma 1 n : ℝ) / n)
      < Real.eulerMascheroniConstant + Real.log (Real.log t) := by linarith
  have hs0 : (0:ℝ) < (ArithmeticFunction.sigma 1 n : ℕ) := by
    exact_mod_cast ArithmeticFunction.sigma_pos 1 n (by omega)
  have := Real.exp_lt_exp.mpr key
  rw [Real.exp_log (by positivity), Real.exp_add, Real.exp_log hlt] at this
  rw [div_lt_iff₀ hn0] at this
  linarith

end RobinRH

-- ===== GLow =====

set_option autoImplicit false
open Finset

namespace RobinRH
open NicCore

lemma S_two (p : ℕ) : S p 2 = 1 + p + (p:ℝ)^2 := by simp [S, Finset.sum_range_succ]

lemma Gf_ge_two (J : ℕ) (hJ : 2 ≤ J) (t : ℝ) (ht : 1 < t) :
    ∑ p ∈ (Icc 2 ⌊t⌋₊).filter Nat.Prime, min (1 / S p 2) (eps t * Real.log p) ≤ Gf J t := by
  unfold Gf
  apply Finset.sum_le_sum
  intro p hp
  have hp2 := (Finset.mem_filter.mp hp).2.two_le
  have hmem : (1:ℕ) ∈ Ico 1 J := by simp; omega
  have := Finset.single_le_sum (f := fun i => min (1 / S p (i+1)) (eps t * Real.log p))
    (s := Ico 1 J) (fun i _ => le_min (by have := S_pos p (i+1); positivity)
      (mul_nonneg (eps_nonneg t ht) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))))) hmem
  simpa using this

/-- Lower bound for the gain `G` via the prime sum `∑ 1/p²` above `Y`. -/
theorem G_lower_Y (J : ℕ) (hJ : 2 ≤ J) (t Y : ℝ) (hY : 2 ≤ Y) (hYt : Y ≤ t)
    (hε : eps t * ((1 + Y + Y^2) * Real.log Y) ≤ 1)
    (ℓ ℓ' : ℝ → ℝ) (hℓ : ∀ u ∈ Set.Icc Y t, ℓ u ≤ Chebyshev.theta u)
    (hd : ∀ u ∈ Set.Icc Y t, HasDerivAt ℓ (ℓ' u) u)
    (hc : ContinuousOn ℓ' (Set.Icc Y t))
    (m : ℝ) (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hm : ∀ u ∈ Set.Icc Y t, m ≤ ℓ' u) :
    eps t * (ℓ Y + m * Y / (1 + 1 / Real.log Y)) - 1 / (t * Real.log t) ≤ Gf J t := by
  have ht1 : 1 < t := by linarith
  have hY1 : 1 < Y := by linarith
  have he0 := eps_nonneg t ht1
  set e := eps t with he
  have hlY : 0 < Real.log Y := Real.log_pos hY1
  have hlt : 0 < Real.log t := Real.log_pos ht1
  have hfY : 2 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY)
  have hfYt : ⌊Y⌋₊ ≤ ⌊t⌋₊ := Nat.floor_le_floor hYt
  set PY := (Icc 2 ⌊Y⌋₊).filter Nat.Prime
  set Q := (Ioc ⌊Y⌋₊ ⌊t⌋₊).filter Nat.Prime
  have hU : (Icc 2 ⌊t⌋₊).filter Nat.Prime = PY ∪ Q := by
    rw [← Finset.filter_union]; congr 1
    ext n; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hD : Disjoint PY Q := by
    apply Finset.disjoint_filter_filter
    rw [Finset.disjoint_left]; intro n h1 h2
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at h1 h2; omega
  have hG := Gf_ge_two J hJ t ht1
  rw [hU, Finset.sum_union hD] at hG
  -- small primes
  have hsmall : ∑ p ∈ PY, e * Real.log p ≤ ∑ p ∈ PY, min (1 / S p 2) (e * Real.log p) := by
    apply Finset.sum_le_sum
    intro p hp
    simp only [PY, Finset.mem_filter, Finset.mem_Icc] at hp
    apply le_min _ le_rfl
    have hp1 : (1:ℝ) < p := by exact_mod_cast hp.2.one_lt
    have hpY : (p:ℝ) ≤ Y := le_trans (by exact_mod_cast hp.1.2) (Nat.floor_le (by linarith))
    have hlp : 0 < Real.log p := Real.log_pos hp1
    have hlpY : Real.log p ≤ Real.log Y := Real.log_le_log (by linarith) hpY
    rw [S_two, le_div_iff₀ (by positivity)]
    have h1 : (1 + p + (p:ℝ)^2) * Real.log p ≤ (1 + Y + Y^2) * Real.log Y := by
      apply mul_le_mul _ hlpY hlp.le (by positivity)
      nlinarith
    calc e * Real.log p * (1 + p + (p:ℝ)^2) = e * ((1 + p + (p:ℝ)^2) * Real.log p) := by ring
      _ ≤ e * ((1 + Y + Y^2) * Real.log Y) := mul_le_mul_of_nonneg_left h1 he0
      _ ≤ 1 := hε
  have hθY : Chebyshev.theta Y = ∑ p ∈ PY, Real.log p := theta_eq_Icc2 Y
  -- large primes
  set c := e * Y^2 * Real.log Y with hc_def
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c ≤ 1 := by
    have : c ≤ e * ((1 + Y + Y^2) * Real.log Y) := by
      rw [hc_def, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ he0
      apply mul_le_mul_of_nonneg_right _ hlY.le
      nlinarith
    linarith
  have hlarge : ∑ p ∈ Q, c * (1/(p:ℝ)^2) ≤ ∑ p ∈ Q, min (1 / S p 2) (e * Real.log p) := by
    apply Finset.sum_le_sum
    intro p hp
    simp only [Q, Finset.mem_filter, Finset.mem_Ioc] at hp
    have hpY : Y < (p:ℝ) := (Nat.floor_lt (by linarith)).mp hp.1.1
    have hp0 : (0:ℝ) < p := by linarith
    apply le_min
    · rw [S_two]
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      have hcY : c * (1 + Y + Y^2) ≤ Y^2 := by
        have : c * (1 + Y + Y^2) = Y^2 * (e * ((1 + Y + Y^2) * Real.log Y)) := by
          rw [hc_def]; ring
        rw [this]; nlinarith [sq_nonneg Y]
      have hY0 : 0 < Y := by linarith
      have key : Y^2 * (1 + p + (p:ℝ)^2) ≤ (p:ℝ)^2 * (1 + Y + Y^2) := by
        nlinarith [mul_pos hp0 hY0]
      have hpos : 0 < 1 + Y + Y^2 := by positivity
      have : c * (1 + p + (p:ℝ)^2) * (1 + Y + Y^2) ≤ (p:ℝ)^2 * (1 + Y + Y^2) := by
        calc c * (1 + p + (p:ℝ)^2) * (1 + Y + Y^2) = c * (1 + Y + Y^2) * (1 + p + (p:ℝ)^2) := by ring
          _ ≤ Y^2 * (1 + p + (p:ℝ)^2) := mul_le_mul_of_nonneg_right hcY (by positivity)
          _ ≤ _ := key
      exact le_of_mul_le_mul_right this hpos
    · have hlp : Real.log Y ≤ Real.log p := Real.log_le_log (by linarith) hpY.le
      rw [hc_def, mul_one_div, div_le_iff₀ (by positivity)]
      have : Y^2 * Real.log Y ≤ (p:ℝ)^2 * Real.log p := by
        apply mul_le_mul _ hlp hlY.le (by positivity); nlinarith
      calc e * Y^2 * Real.log Y = e * (Y^2 * Real.log Y) := by ring
        _ ≤ e * ((p:ℝ)^2 * Real.log p) := mul_le_mul_of_nonneg_left this he0
        _ = e * Real.log p * (p:ℝ)^2 := by ring
  rw [← Finset.mul_sum] at hlarge
  have hA := sum_inv_sq_lower Y t hY hYt ℓ ℓ' hℓ hd hc m hm0 hm
  have hA' := mul_le_mul_of_nonneg_left hA hc0
  -- simplify
  have hfY : c * fq Y = e := by
    rw [hc_def]; unfold fq; field_simp
  have hY2 : c * (Y * Real.log Y)⁻¹ = e * Y := by
    rw [hc_def]; field_simp
  have hk : 0 < 1 + 1 / Real.log Y := by positivity
  have hmk : m / (1 + 1 / Real.log Y) ≤ 1 := by
    rw [div_le_one hk]; have : 0 < 1 / Real.log Y := by positivity
    linarith
  have hmk0 : 0 ≤ m / (1 + 1 / Real.log Y) := by positivity
  have htl : 0 ≤ (t * Real.log t)⁻¹ := by positivity
  have hlast : c * (m / (1 + 1 / Real.log Y)) * (t * Real.log t)⁻¹ ≤ (t * Real.log t)⁻¹ := by
    have : c * (m / (1 + 1 / Real.log Y)) ≤ 1 := by nlinarith
    nlinarith
  have expand : c * (fq Y * (ℓ Y - Chebyshev.theta Y) +
      m / (1 + 1 / Real.log Y) * ((Y * Real.log Y)⁻¹ - (t * Real.log t)⁻¹)) =
      e * (ℓ Y - Chebyshev.theta Y) + m / (1 + 1 / Real.log Y) * (e * Y) -
        c * (m / (1 + 1 / Real.log Y)) * (t * Real.log t)⁻¹ := by
    linear_combination (ℓ Y - Chebyshev.theta Y) * hfY + (m / (1 + 1 / Real.log Y)) * hY2
  rw [expand] at hA'
  have hsm : e * Chebyshev.theta Y = ∑ p ∈ PY, e * Real.log p := by rw [hθY, Finset.mul_sum]
  have e3 : m / (1 + 1 / Real.log Y) * (e * Y) = e * (m * Y / (1 + 1 / Real.log Y)) := by ring
  rw [one_div (t * Real.log t)]
  nlinarith

end RobinRH

-- ===== Tail =====

set_option autoImplicit false
open Finset

namespace RobinFix
open RobinRH NicCore

lemma log1423_lo_cert : 72605 * D ≤ 10000 * logLo 65536 1423 1 := by decide +kernel
lemma log1423_hi_cert : 10000 * logHi 65536 1423 1 ≤ 72607 * D := by decide +kernel

lemma log1423_bounds : 7.2605 ≤ Real.log 1423 ∧ Real.log 1423 ≤ 7.2607 := by
  have h1 := logLo_le 65536 1423 1 (by norm_num) one_pos (by norm_num)
  have h2 := logHi_ge 65536 1423 1 (by norm_num) one_pos (by norm_num)
  have c1 : (72605:ℝ) * D ≤ 10000 * (logLo 65536 1423 1 : ℕ) := by exact_mod_cast log1423_lo_cert
  have c2 : (10000:ℝ) * (logHi 65536 1423 1 : ℕ) ≤ 72607 * D := by exact_mod_cast log1423_hi_cert
  have hD := D_pos
  unfold val at h1 h2
  simp only [Nat.cast_one, div_one, Nat.cast_ofNat] at h1 h2
  constructor
  · have : (7.2605:ℝ) ≤ (logLo 65536 1423 1 : ℕ) / D := by
      rw [le_div_iff₀ hD]; linarith
    linarith
  · have : ((logHi 65536 1423 1 : ℕ):ℝ) / D ≤ 7.2607 := by
      rw [div_le_iff₀ hD]; linarith
    linarith

lemma theta_ge_sqrt (u : ℝ) (h1 : 1423 ≤ u) (h2 : u ≤ 10^8) : u - 2 * Real.sqrt u ≤ Chebyshev.theta u := by
  rcases le_total u (10^4) with h | h
  · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_low u h1 h).le
  rcases le_total u (10^6) with h' | h'
  · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_mid u h h').le
  · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high u h' h2).le

lemma tail_sum (t : ℝ) (ht : 1423 ≤ t) (ht2 : t ≤ 10^8) :
    -(901/10^8 : ℝ) + 0.8556 * (0.0000967 - 1 / (t * Real.log t)) ≤
      ∑ p ∈ (Ioc 1423 ⌊t⌋₊).filter Nat.Prime, 1/(p:ℝ)^2 := by
  have hsq : ∀ u : ℝ, 1423 ≤ u → 37.72 ≤ Real.sqrt u := fun u hu =>
    Real.le_sqrt_of_sq_le (by linarith)
  have hS := sum_inv_sq_lower 1423 t (by norm_num) ht (fun u => u - 2 * Real.sqrt u)
    (fun u => 1 - 1 / Real.sqrt u)
    (fun u hu => theta_ge_sqrt u hu.1 (le_trans hu.2 ht2))
    (fun u hu => by
      have hu0 : 0 < u := by linarith [hu.1]
      have hs := Real.hasDerivAt_sqrt hu0.ne'
      have := (hasDerivAt_id' u).sub (hs.const_mul 2)
      refine this.congr_deriv ?_
      have : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu0
      field_simp)
    (by
      apply ContinuousOn.sub continuousOn_const
      apply ContinuousOn.div continuousOn_const Real.continuous_sqrt.continuousOn
      intro u hu; have := hsq u hu.1; linarith)
    0.97348 (by norm_num)
    (fun u hu => by
      have h1 := hsq u hu.1
      have : 1 / Real.sqrt u ≤ 1 / 37.72 := one_div_le_one_div_of_le (by norm_num) h1
      norm_num at this ⊢; linarith)
  have hfl : ⌊(1423:ℝ)⌋₊ = 1423 := by norm_num
  rw [hfl] at hS
  refine le_trans ?_ hS
  obtain ⟨hL1, hL2⟩ := log1423_bounds
  have hth : Chebyshev.theta 1423 ≤ 1.04 * 1423 :=
    (Chebyshev.theta_le_psi _).trans (TaoFivePrimes.rosser_schoenfeld_psi_le _ (by norm_num))
  have hs1 : Real.sqrt 1423 ≤ 37.73 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  -- first term
  have hA : -(901/10^8 : ℝ) ≤ fq 1423 * (1423 - 2 * Real.sqrt 1423 - Chebyshev.theta 1423) := by
    unfold fq
    have hden : (1423:ℝ)^2 * 7.26 ≤ 1423^2 * Real.log 1423 := by nlinarith
    have hnum : -132.38 ≤ (1423 - 2 * Real.sqrt 1423 - Chebyshev.theta 1423 : ℝ) := by linarith
    have hpos : 0 < (1423:ℝ)^2 * Real.log 1423 := by positivity
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hpos]
    nlinarith
  -- second term
  have htl : 1423 * Real.log 1423 ≤ t * Real.log t :=
    mul_le_mul ht (Real.log_le_log (by norm_num) ht) (by linarith) (by linarith)
  have hd0 : 0 ≤ (1423 * Real.log 1423)⁻¹ - (t * Real.log t)⁻¹ := by
    rw [sub_nonneg]; exact inv_anti₀ (by positivity) htl
  have hc : 0.8556 ≤ 0.97348 / (1 + 1 / Real.log 1423) := by
    rw [le_div_iff₀ (by positivity)]
    have : 1 / Real.log 1423 ≤ 1 / 7.2605 := one_div_le_one_div_of_le (by norm_num) hL1
    norm_num at this ⊢; linarith
  have hY : 0.0000967 ≤ (1423 * Real.log 1423)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) (by positivity)]
    norm_num; nlinarith
  have hB : 0.8556 * (0.0000967 - 1 / (t * Real.log t)) ≤
      0.97348 / (1 + 1 / Real.log 1423) * ((1423 * Real.log 1423)⁻¹ - (t * Real.log t)⁻¹) := by
    rw [one_div]
    calc 0.8556 * (0.0000967 - (t * Real.log t)⁻¹)
        ≤ 0.8556 * ((1423 * Real.log 1423)⁻¹ - (t * Real.log t)⁻¹) := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right hc hd0
  linarith

lemma min_tail (p : ℕ) (hp : 1423 ≤ p) (t e : ℝ) (he0 : 0 ≤ e) (he : e ≤ eps t) :
    min 0.9992 (e * 14700000) * (1 / (p:ℝ)^2) ≤ min (1 / S p 2) (eps t * Real.log p) := by
  have hp' : (1423:ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0:ℝ) < p := by linarith
  rw [S_two]
  apply le_min
  · calc min 0.9992 (e * 14700000) * (1 / (p:ℝ)^2) ≤ 0.9992 * (1 / (p:ℝ)^2) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
      _ ≤ 1 / (1 + p + (p:ℝ)^2) := by
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  · obtain ⟨hL1, _⟩ := log1423_bounds
    have hlp : 7.26 ≤ Real.log p := by linarith [Real.log_le_log (by norm_num : (0:ℝ) < 1423) hp']
    calc min 0.9992 (e * 14700000) * (1 / (p:ℝ)^2) ≤ e * 14700000 * (1 / (p:ℝ)^2) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ ≤ e * 7.26 := by
          have hp2 : (2024929:ℝ) ≤ (p:ℝ)^2 := by nlinarith
          rw [mul_one_div, div_le_iff₀ (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_left hp2 he0]
      _ ≤ eps t * Real.log p := mul_le_mul he hlp (by norm_num) (he0.trans he)

lemma Gf_split (m n : ℕ) (hmn : m ≤ n) (g : ℕ → ℝ) :
    ∑ p ∈ (Icc 2 n).filter Nat.Prime, g p =
      ∑ p ∈ (Icc 2 m).filter Nat.Prime, g p + ∑ p ∈ (Ioc m n).filter Nat.Prime, g p := by
  rw [← Finset.sum_union]
  · congr 1; ext p; simp only [mem_union, mem_filter, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      rcases le_or_gt p m with h | h
      · exact Or.inl ⟨⟨h1, h⟩, h3⟩
      · exact Or.inr ⟨⟨h, h2⟩, h3⟩
    · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨⟨h1, le_trans h2 hmn⟩, h3⟩
      · exact ⟨⟨le_trans (Nat.Prime.two_le h3) le_rfl, h2⟩, h3⟩
  · rw [Finset.disjoint_left]; intro p h1 h2
    simp only [mem_filter, mem_Icc, mem_Ioc] at h1 h2
    exact absurd h1.1.2 (not_le.mpr h2.1.1)

/-- Lower bound for `Gf` on `[1423, 10^8]` via the prime-square tail. -/
theorem Gf_tail (t : ℝ) (ht : 1423 ≤ t) (ht2 : t ≤ 10^8) (e : ℕ) (he : val e ≤ eps t) :
    val (GN e 1423) + min 0.9992 (val e * 14700000) *
      (-(901/10^8 : ℝ) + 0.8556 * (0.0000967 - 1 / (t * Real.log t))) ≤ Gf 8 t := by
  have ht1 : 1 < t := by linarith
  have hft : 1423 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast ht)
  have hG := GN_le e 1423 (by norm_num) t ht1 hft he
  have he0 := val_nonneg e
  -- split Gf
  have hsplit : Gf 8 t = (∑ p ∈ (Icc 2 1423).filter Nat.Prime,
        ∑ i ∈ Ico 1 8, min (1 / S p (i+1)) (eps t * Real.log p)) +
      ∑ p ∈ (Ioc 1423 ⌊t⌋₊).filter Nat.Prime,
        ∑ i ∈ Ico 1 8, min (1 / S p (i+1)) (eps t * Real.log p) := by
    unfold Gf; exact Gf_split 1423 ⌊t⌋₊ hft _
  have hfirst : val (GN e 1423) ≤ ∑ p ∈ (Icc 2 1423).filter Nat.Prime,
        ∑ i ∈ Ico 1 8, min (1 / S p (i+1)) (eps t * Real.log p) :=
    sumP_le _ _ 1423 (by norm_num) (fun p hp _ => gtermN_le e p hp t he)
  set f := min 0.9992 (val e * 14700000) with hf
  have hf0 : 0 ≤ f := le_min (by norm_num) (by positivity)
  have hf1 : f ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have htail : f * ∑ p ∈ (Ioc 1423 ⌊t⌋₊).filter Nat.Prime, 1/(p:ℝ)^2 ≤
      ∑ p ∈ (Ioc 1423 ⌊t⌋₊).filter Nat.Prime,
        ∑ i ∈ Ico 1 8, min (1 / S p (i+1)) (eps t * Real.log p) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    simp only [mem_filter, mem_Ioc] at hp
    have h1 := min_tail p (by omega) t (val e) he0 he
    have hmem : (1:ℕ) ∈ Ico 1 8 := by simp
    have h2 := Finset.single_le_sum (f := fun i => min (1 / S p (i+1)) (eps t * Real.log p))
      (s := Ico 1 8) (fun i _ => le_min (by have := S_pos p (i+1); positivity)
        (mul_nonneg (eps_nonneg t ht1) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))))) hmem
    rw [show (1:ℕ) + 1 = 2 from rfl] at h2
    rw [← hf] at h1
    linarith
  have hT := tail_sum t ht ht2
  set X := -(901/10^8 : ℝ) + 0.8556 * (0.0000967 - 1 / (t * Real.log t))
  set Sm := ∑ p ∈ (Ioc 1423 ⌊t⌋₊).filter Nat.Prime, 1/(p:ℝ)^2
  have : f * X ≤ f * Sm := mul_le_mul_of_nonneg_left hT hf0
  linarith

end RobinFix

-- ===== Consts =====

set_option autoImplicit false
open Finset

namespace NicCore

def ceilH (D n : ℕ) : ℕ := ∑ i ∈ Finset.range n, (D / (i+1) + 1)

lemma inv_le_ceil (D i : ℕ) (hD : 0 < D) :
    (((i:ℝ)+1))⁻¹ ≤ (((D / (i+1) : ℕ) : ℝ) + 1) / D := by
  have h1 := Nat.lt_div_mul_add (a := D) (b := i+1) (by omega)
  have h2 : (D:ℝ) < ((D / (i+1) : ℕ) : ℝ) * ((i:ℝ)+1) + ((i:ℝ)+1) := by exact_mod_cast h1
  have hDp : (0:ℝ) < D := by exact_mod_cast hD
  rw [inv_le_iff_one_le_mul₀ (by positivity), div_mul_eq_mul_div, le_div_iff₀ hDp]
  nlinarith

lemma harmonic_le_ceilH (D n : ℕ) (hD : 0 < D) :
    (harmonic n : ℝ) ≤ (ceilH D n : ℝ) / D := by
  have : (harmonic n : ℝ) = ∑ i ∈ Finset.range n, (((i:ℝ)+1))⁻¹ := by
    simp [harmonic]
  rw [this, ceilH]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  exact inv_le_ceil D i hD

lemma ceilH_1024 : ceilH 1000000000 1024 ≤ 7509177000 := by decide +kernel

lemma gamma_lt' : Real.eulerMascheroniConstant < 0.5778 := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 1024
  simp only [Real.eulerMascheroniSeq', show (1024:ℕ) ≠ 0 by norm_num, if_false] at h
  have hH := harmonic_le_ceilH 1000000000 1024 (by norm_num)
  have hc : (ceilH 1000000000 1024 : ℝ) ≤ 7509177000 := by exact_mod_cast ceilH_1024
  have hl : Real.log (1024:ℕ) = 10 * Real.log 2 := by
    rw [show ((1024:ℕ):ℝ) = 2^10 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_gt_d9
  rw [hl] at h
  have : (ceilH 1000000000 1024 : ℝ) / ((1000000000:ℕ):ℝ) ≤ 7.509177 := by
    rw [div_le_iff₀ (by norm_num)]; push_cast; linarith
  linarith

lemma exp_le_taylor (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.exp x ≤ (∑ m ∈ Finset.range 8, x ^ m / m.factorial) + x ^ 8 * (8 + 1) / ((8:ℕ).factorial * 8) := by
  have := Real.exp_bound' h0 h1 (n := 8) (by norm_num)
  push_cast at this ⊢
  linarith

lemma log_four_pi_gt' : 2.5308 < Real.log (4 * Real.pi) := by
  rw [Real.lt_log_iff_exp_lt (by positivity)]
  have hpi := Real.pi_gt_d6
  have e : Real.exp 2.5308 = Real.exp 1 ^ 2 * Real.exp 0.5308 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have h1 := Real.exp_one_lt_d9
  have h2 := exp_le_taylor 0.5308 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h2
  have h0 := (Real.exp_pos 1).le
  have h3 : Real.exp 1 ^ 2 ≤ (2.7182818286:ℝ)^2 := pow_le_pow_left₀ h0 h1.le 2
  have h4 := Real.exp_pos 0.5308
  rw [e]
  nlinarith

lemma beta_le : βc ≤ 0.047 := by
  have := gamma_lt'; have := log_four_pi_gt'
  unfold βc; linarith

lemma log_two_pi_le : Real.log (2 * Real.pi) ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by positivity)]
  have hpi := Real.pi_lt_d2
  have := Real.add_one_le_exp (1:ℝ)
  have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h1 := Real.exp_one_gt_d9
  nlinarith

end NicCore

-- ===== RegA =====

set_option autoImplicit false
open Finset

namespace RobinFix
open RobinRH NicCore

def BETA : ℕ := fdivU 47 1000
def C104 : ℕ := fdivU 104 100
def C1N : ℕ := fdivU 901 (10^8)
def C2N : ℕ := fdivL 8556 (10^4)
def C3N : ℕ := fdivL 967 (10^7)
def KAPN : ℕ := fdivL 9992 (10^4)
def C0N : ℕ := 14700000 * D

def gN (invL bn bd : ℕ) : ℕ := invL - fmulL (fdivL bn bd) (fmulL invL invL)

def EupN (A r2 r23 r45 : ℕ) : ℕ :=
  let invL := fdivU D (logLo QL A 1)
  let v := invL + fmulU invL invL
  let i2 := fdivU D r2
  let i23 := fdivU D r23
  let i45 := fdivU D r45
  fmulU (2 * fmulU BETA i2 + fdivU 2 A) v +
  fmulU C104 (fmulU (2 * i2) (gN invL 3 5) + fmulU (cdiv (3 * i23) 2) (gN invL 1 3)
    + fmulU (cdiv (5 * i45) 4) (gN invL 1 6)) +
  fmulU (fdivU 4 (100 * A)) invL

def regAchk (A B r2 r23 r45 : ℕ) : Bool :=
  let lam := logLo QL A 1
  let invL := fdivU D lam
  let e := fdivL D ((B + 1) * logHi QL B 1)
  let E := EupN A r2 r23 r45
  decide (1000 ≤ A) && decide (A < B) && decide (B ≤ 10^8) && decide (D ≤ lam) &&
  decide (invL * 6 ≤ D * 5) && decide (0 < r2) && decide (0 < r23) && decide (0 < r45) &&
  decide (Nat.pow r2 2 ≤ A * Nat.pow D 2) && decide (Nat.pow r23 3 ≤ Nat.pow A 2 * Nat.pow D 3) &&
  decide (Nat.pow r45 5 ≤ Nat.pow A 4 * Nat.pow D 5) &&
  (if A < 1500 then decide (E < GN e (min A 1423)) else
    let u := fdivU D (A * lam)
    let pos := fmulL C2N (C3N - u)
    decide (u ≤ C3N) &&
    decide (E + (C1N - pos) < GN e 1423 + fmulL (min KAPN (fmulL e C0N)) (pos - C1N)))

lemma val_fdivU_inv (x : ℕ) (hx : 0 < x) : 1 / val x ≤ val (fdivU D x) := by
  have := val_fdivU D x hx
  refine le_trans (le_of_eq ?_) this
  unfold val; have := D_pos; have : (0:ℝ) < x := by exact_mod_cast hx
  field_simp

lemma rpow_cert (A : ℕ) (hA : 0 < A) (t : ℝ) (hAt : (A:ℝ) ≤ t) (α : ℝ) (p q R : ℕ)
    (hq : 0 < q) (hα : α = (p:ℝ) / q) (hR : 0 < R)
    (hc : Nat.pow R q ≤ Nat.pow A p * Nat.pow D q) :
    t ^ (-α) ≤ val (fdivU D R) := by
  have hA' : (0:ℝ) < A := by exact_mod_cast hA
  have ht0 : 0 < t := lt_of_lt_of_le hA' hAt
  have hD := D_pos
  have hR' : (0:ℝ) < R := by exact_mod_cast hR
  have hvR : 0 < val R := by unfold val; positivity
  have h1 : (val R)^q ≤ (A:ℝ)^p := by
    have : ((R^q : ℕ):ℝ) ≤ ((A^p * D^q : ℕ):ℝ) := by
      simp only [Nat.pow_eq] at hc; exact_mod_cast hc
    push_cast at this
    unfold val; rw [div_pow, div_le_iff₀ (by positivity)]; exact this
  have h2 : val R ≤ ((A:ℝ)^p) ^ ((q:ℝ)⁻¹) := by
    have := Real.rpow_le_rpow (by positivity) h1 (by positivity : (0:ℝ) ≤ (q:ℝ)⁻¹)
    rwa [Real.pow_rpow_inv_natCast hvR.le hq.ne'] at this
  have h3 : ((A:ℝ)^p) ^ ((q:ℝ)⁻¹) = (A:ℝ) ^ α := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA'.le, hα, div_eq_mul_inv]
  have h4 : (A:ℝ) ^ α ≤ t ^ α := by
    apply Real.rpow_le_rpow hA'.le hAt
    rw [hα]; positivity
  rw [Real.rpow_neg ht0.le]
  have h5 : (t ^ α)⁻¹ ≤ (val R)⁻¹ := inv_anti₀ hvR (by linarith)
  refine h5.trans ?_
  have := val_fdivU_inv R hR
  rwa [one_div] at this

lemma Fk_le' (α b t : ℝ) (hα : 0 < α) (hb0 : 0 ≤ b) (ht : 1 < t) (I x : ℝ)
    (hI : t ^ (-α) ≤ I) (hx : 1 / Real.log t ≤ x) (hxb : 2 * b * x ≤ 1) :
    Fk α b t ≤ I / α * (x - b * x^2) := by
  unfold Fk
  have hl := Real.log_pos ht
  set y := 1 / Real.log t with hy
  have hy0 : 0 < y := by positivity
  have hg : 1 / Real.log t - b / Real.log t ^ 2 = y - b * y^2 := by rw [hy]; field_simp
  rw [hg]
  have hg0 : 0 ≤ y - b * y^2 := by nlinarith
  have hby : b * (x + y) ≤ 1 := by nlinarith
  have hgx : y - b * y^2 ≤ x - b * x^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hby)]
  have htα : 0 ≤ t ^ (-α) := by positivity
  calc t ^ (-α) / α * (y - b * y^2) ≤ I / α * (y - b * y^2) := by gcongr
    _ ≤ I / α * (x - b * x^2) := by
      apply mul_le_mul_of_nonneg_left hgx
      exact div_nonneg (htα.trans hI) hα.le

lemma gN_ge (invL bn bd : ℕ) (hbd : 0 < bd) :
    val invL - (bn:ℝ)/bd * (val invL)^2 ≤ val (gN invL bn bd) := by
  unfold gN
  refine le_trans ?_ (val_sub_le _ _)
  have h1 := val_fmulL (fdivL bn bd) (fmulL invL invL)
  have h2 := val_fdivL bn bd
  have h3 := val_fmulL invL invL
  have h4 := val_nonneg (fdivL bn bd)
  have h5 := val_nonneg (fmulL invL invL)
  have : val (fdivL bn bd) * val (fmulL invL invL) ≤ (bn:ℝ)/bd * (val invL)^2 := by
    rw [sq]; exact mul_le_mul h2 h3 h5 (by positivity)
  linarith

lemma val_cdiv (x c : ℕ) (hc : 0 < c) : val x / c ≤ val (cdiv x c) := by
  have := cdiv_ge x c hc
  unfold val; have hD := D_pos
  rw [div_div, mul_comm, ← div_div]
  exact div_le_div_of_nonneg_right this hD.le

set_option maxHeartbeats 1000000 in
theorem Eup_bound (hRH : RiemannHypothesis) (A r2 r23 r45 : ℕ) (hA : 1000 ≤ A)
    (hlam : D ≤ logLo QL A 1) (hinv : fdivU D (logLo QL A 1) * 6 ≤ D * 5)
    (h2 : 0 < r2) (h23 : 0 < r23) (h45 : 0 < r45)
    (c2 : Nat.pow r2 2 ≤ A * Nat.pow D 2) (c23 : Nat.pow r23 3 ≤ Nat.pow A 2 * Nat.pow D 3)
    (c45 : Nat.pow r45 5 ≤ Nat.pow A 4 * Nat.pow D 5)
    (t : ℝ) (hAt : (A:ℝ) ≤ t) :
    E1 t + E2 t + 0.04 / (t * Real.log t) ≤ val (EupN A r2 r23 r45) := by
  have hA0 : 0 < A := by omega
  have hA' : (1000:ℝ) ≤ A := by exact_mod_cast hA
  have ht1 : 1 < t := by linarith
  have ht0 : 0 < t := by linarith
  have hlt := Real.log_pos ht1
  set lam := logLo QL A 1 with hlamdef
  set invL := fdivU D lam with hinvdef
  have hDpos : 0 < D := by unfold D; norm_num
  have hlam0 : 0 < lam := lt_of_lt_of_le hDpos hlam
  have hvlam : 0 < val lam := by unfold val; have := D_pos; positivity
  have hlamt : val lam ≤ Real.log t := by
    have := logLo_le QL A 1 (by unfold QL; norm_num) one_pos (by omega)
    simp only [Nat.cast_one, div_one] at this
    exact this.trans (Real.log_le_log (by linarith) hAt)
  set x := val invL with hx
  have hx1 : 1 / Real.log t ≤ x := by
    have := val_fdivU_inv lam hlam0
    exact le_trans (one_div_le_one_div_of_le hvlam hlamt) this
  have hx56 : x ≤ 5/6 := by
    have h := val_le hinv
    have hD := D_pos
    unfold val at h; push_cast at h
    have h' : (invL:ℝ) * 6 ≤ D * 5 := (div_le_div_iff_of_pos_right hD).mp h
    rw [hx]; unfold val; rw [div_le_iff₀ hD]; linarith
  have hx0 : 0 ≤ x := val_nonneg _
  -- rpow bounds
  have hr2 := rpow_cert A hA0 t hAt (1/2) 1 2 r2 (by norm_num) (by norm_num) h2 (by simpa using c2)
  have hr23 := rpow_cert A hA0 t hAt (2/3) 2 3 r23 (by norm_num) (by norm_num) h23 c23
  have hr45 := rpow_cert A hA0 t hAt (4/5) 4 5 r45 (by norm_num) (by norm_num) h45 c45
  set i2 := fdivU D r2
  set i23 := fdivU D r23
  set i45 := fdivU D r45
  -- E1
  have hβ0 := beta_nonneg hRH
  have hβ := beta_le
  have hBETA : (0.047:ℝ) ≤ val BETA := by
    have h := val_fdivU 47 1000 (by norm_num)
    have e : ((47:ℕ):ℝ) / ((1000:ℕ):ℝ) = 0.047 := by norm_num
    unfold BETA; linarith
  have hl2 := log_two_pi_le
  have hl2' : 0 ≤ Real.log (2*Real.pi) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hE1 : E1 t ≤ val (fmulU (2 * fmulU BETA i2 + fdivU 2 A) (invL + fmulU invL invL)) := by
    unfold E1
    refine le_trans ?_ (val_fmulU _ _)
    have hv : vfun t ≤ val (invL + fmulU invL invL) := by
      unfold vfun; rw [val_add]
      have := val_fmulU invL invL
      have : 1 / Real.log t ^ 2 ≤ x * x := by
        rw [show 1 / Real.log t ^ 2 = (1 / Real.log t) * (1 / Real.log t) by ring]
        exact mul_le_mul hx1 hx1 (by positivity) hx0
      linarith
    have hv0 : 0 ≤ vfun t := by unfold vfun; have := Real.log_pos ht1; positivity
    have hc : 2 * βc * t ^ (-(1/2:ℝ)) + Real.log (2*Real.pi) / t ≤ val (2 * fmulU BETA i2 + fdivU 2 A) := by
      rw [val_add]
      have h1 : val (2 * fmulU BETA i2) = 2 * val (fmulU BETA i2) := by unfold val; push_cast; ring
      rw [h1]
      have h3 := val_fmulU BETA i2
      have h4 : βc * t ^ (-(1/2:ℝ)) ≤ val BETA * val i2 :=
        mul_le_mul (by linarith) hr2 (by positivity) (val_nonneg _)
      have h5 : Real.log (2*Real.pi) / t ≤ val (fdivU 2 A) := by
        refine le_trans ?_ (val_fdivU 2 A hA0)
        push_cast
        calc Real.log (2*Real.pi) / t ≤ 2 / t := by gcongr
          _ ≤ 2 / A := by gcongr
      linarith
    exact mul_le_mul hc hv hv0 (val_nonneg _)
  -- E2
  have hg := fun (bn bd : ℕ) (hbd : 0 < bd) => gN_ge invL bn bd hbd
  have F1 := Fk_le' (1/2) (3/5) t (by norm_num) (by norm_num) ht1 (val i2) x hr2 hx1 (by nlinarith)
  have F2 := Fk_le' (2/3) (1/3) t (by norm_num) (by norm_num) ht1 (val i23) x hr23 hx1 (by nlinarith)
  have F3 := Fk_le' (4/5) (1/6) t (by norm_num) (by norm_num) ht1 (val i45) x hr45 hx1 (by nlinarith)
  have hgpos : ∀ b : ℝ, 0 ≤ b → b ≤ 3/5 → 0 ≤ x - b * x^2 := fun b h0 h1 => by nlinarith
  have T1 : val i2 / (1/2) * (x - 3/5 * x^2) ≤ val (fmulU (2 * i2) (gN invL 3 5)) := by
    refine le_trans ?_ (val_fmulU _ _)
    have : val (2 * i2) = val i2 / (1/2) := by unfold val; push_cast; ring
    rw [this]
    apply mul_le_mul_of_nonneg_left _ (by have := val_nonneg i2; positivity)
    have := hg 3 5 (by norm_num); push_cast at this; linarith
  have T2 : val i23 / (2/3) * (x - 1/3 * x^2) ≤ val (fmulU (cdiv (3 * i23) 2) (gN invL 1 3)) := by
    refine le_trans ?_ (val_fmulU _ _)
    have h1 := val_cdiv (3 * i23) 2 (by norm_num)
    have : val (3 * i23) / ((2:ℕ):ℝ) = val i23 / (2/3) := by unfold val; push_cast; ring
    rw [this] at h1
    have := hg 1 3 (by norm_num); push_cast at this
    exact mul_le_mul h1 (by linarith) (hgpos _ (by norm_num) (by norm_num)) (val_nonneg _)
  have T3 : val i45 / (4/5) * (x - 1/6 * x^2) ≤ val (fmulU (cdiv (5 * i45) 4) (gN invL 1 6)) := by
    refine le_trans ?_ (val_fmulU _ _)
    have h1 := val_cdiv (5 * i45) 4 (by norm_num)
    have : val (5 * i45) / ((4:ℕ):ℝ) = val i45 / (4/5) := by unfold val; push_cast; ring
    rw [this] at h1
    have := hg 1 6 (by norm_num); push_cast at this
    exact mul_le_mul h1 (by linarith) (hgpos _ (by norm_num) (by norm_num)) (val_nonneg _)
  have hC104 : (1.04:ℝ) ≤ val C104 := by
    have h := val_fdivU 104 100 (by norm_num)
    have e : ((104:ℕ):ℝ) / ((100:ℕ):ℝ) = 1.04 := by norm_num
    unfold C104; linarith
  have hE2 : E2 t ≤ val (fmulU C104 (fmulU (2 * i2) (gN invL 3 5) + fmulU (cdiv (3 * i23) 2) (gN invL 1 3)
      + fmulU (cdiv (5 * i45) 4) (gN invL 1 6))) := by
    unfold E2
    refine le_trans ?_ (val_fmulU _ _)
    rw [val_add, val_add]
    have hs0 : 0 ≤ Fk (1/2) (3/5) t + Fk (2/3) (1/3) t + Fk (4/5) (1/6) t := by
      unfold Fk
      have hl := Real.log_pos ht1
      have hy : ∀ b : ℝ, b ≤ 3/5 → 0 ≤ 1 / Real.log t - b / Real.log t ^ 2 := fun b hb => by
        have h6 := log_ge_six t (by linarith)
        rw [div_sub_div _ _ hl.ne' (by positivity), le_div_iff₀ (by positivity)]
        nlinarith
      have k : ∀ α b : ℝ, 0 < α → b ≤ 3/5 →
          0 ≤ t ^ (-α) / α * (1 / Real.log t - b / Real.log t ^ 2) := fun α b hα hb =>
        mul_nonneg (div_nonneg (Real.rpow_nonneg ht0.le _) hα.le) (hy b hb)
      have := k (1/2) (3/5) (by norm_num) (by norm_num)
      have := k (2/3) (1/3) (by norm_num) (by norm_num)
      have := k (4/5) (1/6) (by norm_num) (by norm_num)
      linarith
    apply mul_le_mul hC104 (by linarith) hs0 (val_nonneg _)
  -- E3
  have hE3 : 0.04 / (t * Real.log t) ≤ val (fmulU (fdivU 4 (100 * A)) invL) := by
    refine le_trans ?_ (val_fmulU _ _)
    have h1 : (0.04:ℝ) / t ≤ val (fdivU 4 (100 * A)) := by
      refine le_trans ?_ (val_fdivU 4 (100 * A) (by omega))
      push_cast
      rw [div_le_div_iff₀ ht0 (by positivity)]; nlinarith
    calc (0.04:ℝ) / (t * Real.log t) = 0.04 / t * (1 / Real.log t) := by field_simp
      _ ≤ _ := mul_le_mul h1 hx1 (by positivity) (val_nonneg _)
  unfold EupN
  simp only [← hlamdef, ← hinvdef]
  rw [val_add, val_add]
  linarith


lemma tail_combine (f X : ℝ) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (fl pos : ℕ)
    (hfl : val fl ≤ f) (hX : val pos - val C1N ≤ X) :
    val (fmulL fl (pos - C1N)) - val (C1N - pos) ≤ f * X := by
  rcases le_total C1N pos with h | h
  · have e1 : C1N - pos = 0 := Nat.sub_eq_zero_of_le h
    have e2 : val (pos - C1N) = val pos - val C1N := by
      unfold val; push_cast [h]; ring
    rw [e1]
    have h1 := val_fmulL fl (pos - C1N)
    have h2 : 0 ≤ val (pos - C1N) := val_nonneg _
    have h3 : val fl * val (pos - C1N) ≤ f * X :=
      mul_le_mul hfl (by linarith) h2 hf0
    have h0 : val 0 = 0 := by unfold val; simp
    rw [h0]
    linarith
  · have e1 : pos - C1N = 0 := Nat.sub_eq_zero_of_le h
    have e2 : val (C1N - pos) = val C1N - val pos := by
      unfold val; push_cast [h]; ring
    rw [e1, e2]
    have : fmulL fl 0 = 0 := by simp [fmulL]
    rw [this]
    have h0 : val 0 = 0 := by simp [val]
    rw [h0]
    have hle := val_le h
    rcases le_total 0 X with hX0 | hX0
    · have := mul_nonneg hf0 hX0; linarith
    · have : X ≤ f * X := by nlinarith
      linarith

theorem regAchk_sound (hRH : RiemannHypothesis) (A B r2 r23 r45 : ℕ)
    (hc : regAchk A B r2 r23 r45 = true) (t : ℝ) (h1 : (A:ℝ) ≤ t) (h2 : t < B) :
    E1 t + E2 t + 0.04 / (t * Real.log t) < Gf 8 t := by
  unfold regAchk at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hA, hAB⟩, hB8⟩, hlam⟩, hinv⟩, hr2⟩, hr23⟩, hr45⟩, c2⟩, c23⟩, c45⟩, hG⟩ := hc
  have hE := Eup_bound hRH A r2 r23 r45 hA hlam hinv hr2 hr23 hr45 c2 c23 c45 t h1
  have hA' : (1000:ℝ) ≤ A := by exact_mod_cast hA
  have ht1 : 1 < t := by linarith
  have ht0 : 0 < t := by linarith
  have hlt := Real.log_pos ht1
  have hB0 : 0 < B := by omega
  -- eps lower bound
  set e := fdivL D ((B + 1) * logHi QL B 1) with he_def
  have hlB : Real.log t ≤ val (logHi QL B 1) := by
    have := logHi_ge QL B 1 (by unfold QL; norm_num) one_pos hB0
    simp only [Nat.cast_one, div_one] at this
    exact (Real.log_le_log ht0 h2.le).trans this
  have he : val e ≤ eps t := by
    refine le_trans ?_ (eps_ge t ht1)
    have hvB : 0 < val (logHi QL B 1) := lt_of_lt_of_le hlt hlB
    refine (val_fdivL _ _).trans ?_
    have hD := D_pos
    have hden : (t + 1) * Real.log t ≤ ((B:ℝ) + 1) * val (logHi QL B 1) :=
      mul_le_mul (by linarith) hlB hlt.le (by positivity)
    calc ((D:ℕ):ℝ) / (((B + 1) * logHi QL B 1 : ℕ):ℝ) = 1 / (((B:ℝ) + 1) * val (logHi QL B 1)) := by
          unfold val; push_cast; field_simp
      _ ≤ 1 / ((t + 1) * Real.log t) := one_div_le_one_div_of_le (by positivity) hden
  split_ifs at hG with hA15
  all_goals simp only [Bool.and_eq_true, decide_eq_true_eq] at hG
  · -- no tail
    have hP : min A 1423 ≤ ⌊t⌋₊ := le_trans (min_le_left _ _) (Nat.le_floor h1)
    have := GN_le e (min A 1423) (by omega) t ht1 hP he
    have := val_lt hG
    linarith
  · obtain ⟨hu, hG⟩ := hG
    set lam := logLo QL A 1 with hlamdef
    set u := fdivU D (A * lam) with hudef
    set pos := fmulL C2N (C3N - u) with hposdef
    have hA15' : (1500:ℝ) ≤ A := by exact_mod_cast (not_lt.mp hA15)
    have hT := Gf_tail t (by linarith) (by
      have : (B:ℝ) ≤ 10^8 := by exact_mod_cast hB8
      linarith) e he
    -- 1/(t log t) ≤ val u
    have hDpos : 0 < D := by unfold D; norm_num
    have hlam0 : 0 < lam := lt_of_lt_of_le hDpos hlam
    have hvlam : 0 < val lam := div_pos (by exact_mod_cast hlam0) D_pos
    have hlamt : val lam ≤ Real.log t := by
      have := logLo_le QL A 1 (by unfold QL; norm_num) one_pos (by omega)
      simp only [Nat.cast_one, div_one] at this
      exact this.trans (Real.log_le_log (by linarith) h1)
    have hvu : 1 / (t * Real.log t) ≤ val u := by
      have := val_fdivU_inv (A * lam) (by positivity)
      refine le_trans ?_ this
      have : val (A * lam) = A * val lam := by unfold val; push_cast; ring
      rw [this]
      apply one_div_le_one_div_of_le (by positivity)
      exact mul_le_mul h1 hlamt hvlam.le (by linarith)
    have hC2 : val C2N ≤ 0.8556 := by
      have h := val_fdivL 8556 (10^4)
      have e : ((8556:ℕ):ℝ) / ((10^4:ℕ):ℝ) = 0.8556 := by norm_num
      unfold C2N; linarith
    have hC3 : val C3N ≤ 0.0000967 := by
      have h := val_fdivL 967 (10^7)
      have e : ((967:ℕ):ℝ) / ((10^7:ℕ):ℝ) = 0.0000967 := by norm_num
      unfold C3N; linarith
    have hC1 : (901/10^8:ℝ) ≤ val C1N := by
      have h := val_fdivU 901 (10^8) (by norm_num)
      have e : ((901:ℕ):ℝ) / ((10^8:ℕ):ℝ) = 901/10^8 := by norm_num
      unfold C1N; linarith
    have hKAP : val KAPN ≤ 0.9992 := by
      have h := val_fdivL 9992 (10^4)
      have e : ((9992:ℕ):ℝ) / ((10^4:ℕ):ℝ) = 0.9992 := by norm_num
      unfold KAPN; linarith
    have hC0 : val C0N = 14700000 := by unfold C0N val; push_cast; field_simp
    have hX : val pos - val C1N ≤ -(901/10^8 : ℝ) + 0.8556 * (0.0000967 - 1 / (t * Real.log t)) := by
      have hsub : val (C3N - u) = val C3N - val u := by unfold val; push_cast [hu]; ring
      have hp := val_fmulL C2N (C3N - u)
      have hnn : 0 ≤ val (C3N - u) := val_nonneg _
      have : val C2N * val (C3N - u) ≤ 0.8556 * (0.0000967 - 1 / (t * Real.log t)) := by
        apply mul_le_mul hC2 (by linarith) hnn (by norm_num)
      linarith
    set f := min 0.9992 (val e * 14700000)
    have hf0 : 0 ≤ f := le_min (by norm_num) (by have := val_nonneg e; positivity)
    have hf1 : f ≤ 1 := (min_le_left _ _).trans (by norm_num)
    have hfl : val (min KAPN (fmulL e C0N)) ≤ f := by
      rw [val_min]
      apply min_le_min hKAP
      have := val_fmulL e C0N; rw [hC0] at this; exact this
    have hcomb := tail_combine f _ hf0 hf1 _ pos hfl hX
    have hG' := val_lt hG
    rw [val_add, val_add] at hG'
    linarith

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

-- ===== RegAAll =====

set_option autoImplicit false

namespace RobinFix
open RobinRH NicCore

def regAList : List (ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (1000, 1167, 583337266871351588485, 1844674407370955161600, 4633612614428078043356),
  (1167, 1371, 630166265517867266025, 2044718971535109016066, 5242958345581110342986),
  (1371, 1423, 683027909421428132470, 2276554363948047036415, 5964165501560178836732),
  (1423, 1500, 695860480361182340300, 2333760702168692879899, 6144458885388836383996),
  (1500, 1794, 714439325892274560473, 2417207289117413565151, 6409036275758495034050),
  (1794, 2175, 781323598937190430651, 2723545792040569370745, 7395672538489594709442),
  (2175, 2678, 860298871354043540821, 3096653148153742260358, 8627542980498098491792),
  (2678, 3327, 954607866411267954597, 3557351428195731064365, 10189859141829857351959),
  (3327, 4183, 1064011012511600966250, 4111070486678856102223, 12121656227951572441835),
  (4183, 5316, 1193063762265154708720, 4789001417045517079025, 14558278197583282784171),
  (5316, 6784, 1344968796125660631220, 5618793060087756720322, 17635496875594234333482),
  (6784, 8724, 1519366834306859067598, 6610641646737206853586, 21434255037141235172173),
  (8724, 11329, 1722969346511500521783, 7817420867699646680759, 26211522517160161071872),
  (11329, 14855, 1963430399797077567031, 9304951354669502114278, 32305240900904996334789),
  (14855, 19708, 2248309267118414222088, 11147260747935071749177, 40125258880462792771869),
  (19708, 26416, 2589649568431577430662, 13459060899679361113930, 50307619255792483972673),
  (26416, 35637, 2998149263226150728806, 16361800504421982134523, 63593593611237154264426),
  (35637, 48122, 3482332940711080833922, 19976549719566812252836, 80805446087419844994354),
  (48122, 65324, 4046611923692386979025, 24405188609374866990497, 102753034783835420938965),
  (65324, 89130, 4714722190834088178436, 29920457918722489238007, 131213324326348220916901),
  (89130, 121671, 5507210488410920112294, 36807444014140310060656, 168243714320385221644573),
  (121671, 166048, 6434477124494072190271, 45294392672437412297935, 215808916586595723636733),
  (166048, 226462, 7516861476872378149196, 55728260665517544075510, 276762115579488374958634),
  (226462, 307317, 8778440942311428816624, 68535662431810555454599, 354744763378789088275759),
  (307317, 414811, 10226170160673156223704, 84006091525632899465848, 452886098944706534553949),
  (414811, 555289, 11880777285381685201439, 102601387101693413605915, 575704910921497758194089),
  (555289, 734339, 13746092362746621616274, 124623258580565873616130, 727000950745823345403928),
  (734339, 958550, 15807675763449699195668, 150147273964888400689914, 909153044716921857551742),
  (958550, 1160496, 18060389331685670063292, 179334110703173034300561, 1125152889204769502990652)]

lemma regAList_chain : chainOK (regAList.map (fun q => (q.1, q.2.1))) 1000 1160496 = true := by
  decide +kernel

lemma regAList_ok : regAList.all (fun q => regAchk q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) = true := by
  decide +kernel

theorem gap_regA (hRH : RiemannHypothesis) (t : ℝ) (h1 : 1000 ≤ t) (h2 : t < 1100000) :
    E1 t + E2 t + 0.04 / (t * Real.log t) < Gf 8 t := by
  obtain ⟨p, hp, hp1, hp2⟩ := cover (regAList.map (fun q => (q.1, q.2.1))) 1000 1160496
    regAList_chain 1 one_pos t (by norm_num; linarith) (by norm_num; linarith)
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  simp only [div_one] at hp1 hp2
  exact regAchk_sound hRH _ _ _ _ _ (List.all_eq_true.mp regAList_ok q hq) t hp1 hp2

end RobinFix

-- ===== PubMid =====

set_option autoImplicit false

namespace RobinRHParts

theorem robin_RH_logrange_1000_1100000 (hRH : RiemannHypothesis) :
    ∀ n : ℕ, (1000:ℝ) ≤ Real.log n → Real.log n < 1100000 →
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by
  intro n h1 h2
  exact RobinRH.robin_of_gap hRH 8 n h1 (RobinFix.gap_regA hRH _ h1 h2)

end RobinRHParts

theorem solution (hRH : RiemannHypothesis) :
    ∀ n : ℕ, (1000:ℝ) ≤ Real.log n → Real.log n < 1100000 →
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) :=
  RobinRHParts.robin_RH_logrange_1000_1100000 hRH
