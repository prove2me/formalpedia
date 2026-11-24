-- Prove2me | solution 1 for RobinRHParts.robin_logrange_487_1009
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-24T03:17:17.482826+00:00
-- url     : https://prove2.me/submissions/f7d4e2d2-9608-4123-8ba9-3fff62e5a53a

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

-- ===== FinReg =====

set_option autoImplicit false
open Finset

namespace RobinFix
open RobinRH

/-- the finite-range checker on `[A/1000, B/1000)` -/
def finchk (A B : ℕ) : Bool :=
  let a0 := A / 1000
  let lA := logLo QL A 1000
  let epsHi := fdivU (mlogHi 1000 (A + 1000) 6) lA
  let epsLo := fdivL (mlogLo 1000 (B + 1000) 6) (logHi QL B 1000)
  let th := sumP (fun p => logLo QL p 1) a0
  let ML := sumP (fun p => mlogHi 1 p 24) a0
  decide (10000 ≤ A) && decide ((B - 1) / 1000 < 4225) && decide (D ≤ lA) &&
  (List.range' (a0 + 1) ((B - 1) / 1000 - a0)).all (fun q => !primeB q) &&
  decide (fmulU epsHi (fdivU B 1000 - th) + ML < GAM + logLo QL lA D + GN epsLo a0)

lemma fdivL_le_div (x y : ℕ) : val (fdivL x y) ≤ val x / val y := by
  refine (val_fdivL x y).trans (le_of_eq ?_)
  unfold val; have := D_pos; rcases Nat.eq_zero_or_pos y with h | h
  · subst h; simp
  · field_simp

lemma div_le_fdivU (x y : ℕ) (hy : 0 < y) : val x / val y ≤ val (fdivU x y) := by
  refine le_trans (le_of_eq ?_) (val_fdivU x y hy)
  unfold val; have := D_pos; field_simp

lemma log_one_add_inv (A M : ℕ) (hA : 0 < A) (hM : 0 < M) :
    Real.log (1 + 1 / ((A:ℝ) / M)) = -Real.log (1 - (M:ℝ) / ((A + M : ℕ) : ℝ)) := by
  have hA' : (0:ℝ) < A := by exact_mod_cast hA
  have hM' : (0:ℝ) < M := by exact_mod_cast hM
  rw [← Real.log_inv]
  congr 1
  push_cast
  have h3 : (A:ℝ) + M ≠ 0 := by positivity
  have e : 1 - (M:ℝ) / (A + M) = A / (A + M) := by field_simp; ring
  rw [e, inv_div]
  field_simp

lemma floor_bounds (A B : ℕ) (t : ℝ) (h1 : (A:ℝ) / 1000 ≤ t) (h2 : t < (B:ℝ) / 1000) :
    A / 1000 ≤ ⌊t⌋₊ ∧ ⌊t⌋₊ ≤ (B - 1) / 1000 := by
  have ht0 : 0 ≤ t := le_trans (by positivity) h1
  constructor
  · apply Nat.le_floor
    have := floor_le A 1000
    push_cast at this ⊢; linarith
  · have hf := Nat.floor_le ht0
    have : ((⌊t⌋₊ * 1000 : ℕ) : ℝ) < B := by push_cast; linarith
    have : ⌊t⌋₊ * 1000 < B := by exact_mod_cast this
    omega

theorem finchk_sound (A B : ℕ) (hc : finchk A B = true) (n : ℕ)
    (h1 : (A:ℝ) / 1000 ≤ Real.log n) (h2 : Real.log n < (B:ℝ) / 1000) :
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) <
      Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by
  unfold finchk at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range',
    Bool.not_eq_true'] at hc
  obtain ⟨⟨⟨⟨hA, hB⟩, hDl⟩, hnp⟩, hmain⟩ := hc
  set t := Real.log n with htdef
  set a0 := A / 1000
  set lA := logLo QL A 1000
  set epsHi := fdivU (mlogHi 1000 (A + 1000) 6) lA
  set epsLo := fdivL (mlogLo 1000 (B + 1000) 6) (logHi QL B 1000)
  set th := sumP (fun p => logLo QL p 1) a0
  set ML := sumP (fun p => mlogHi 1 p 24) a0
  have hA' : (10:ℝ) ≤ (A:ℝ) / 1000 := by
    rw [le_div_iff₀ (by norm_num)]; exact_mod_cast (by omega : 10 * 1000 ≤ A)
  have ht10 : 10 ≤ t := by linarith
  have hn0 : (0:ℝ) < n := by
    by_contra h; push_neg at h
    have : (n:ℝ) = 0 := le_antisymm h (Nat.cast_nonneg n)
    rw [htdef, this, Real.log_zero] at ht10; linarith
  have hn3 : 3 ≤ n := by
    by_contra h; push_neg at h
    have : (n:ℝ) ≤ 2 := by exact_mod_cast (by omega : n ≤ 2)
    have := Real.log_le_sub_one_of_pos hn0
    linarith
  have hloc := local_bound 8 n hn3
  rw [← htdef] at hloc
  obtain ⟨hf1, hf2⟩ := floor_bounds A B t h1 h2
  -- the prime set is that up to a0
  have hset : (Icc 2 ⌊t⌋₊).filter Nat.Prime = (Icc 2 a0).filter Nat.Prime := by
    ext p; simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨h2p, hpt⟩, hp⟩
      refine ⟨⟨h2p, ?_⟩, hp⟩
      by_contra hcon; push_neg at hcon
      have := hnp p ⟨p - (a0 + 1), by omega, by omega⟩
      have hpB := (primeB_iff p (by omega)).mpr hp
      rw [hpB] at this; exact absurd this (by decide)
    · rintro ⟨⟨h2p, hpa⟩, hp⟩; exact ⟨⟨h2p, by omega⟩, hp⟩
  have hB0 : a0 < 4225 := by omega
  -- theta lower bound
  have hth : val th ≤ Chebyshev.theta t := by
    rw [theta_eq_Icc2, hset]
    exact sumP_le _ _ a0 hB0 (fun p hp _ => logLo_prime_le p hp.one_lt.le)
  -- L upper bound
  have hL : Lf t ≤ val ML := by
    unfold Lf; rw [hset]
    refine sumP_ge _ _ a0 hB0 (fun p hp _ => ?_)
    have := mlogHi_ge 1 p 24 hp.one_lt
    simpa using this
  -- eps bounds
  have ht1 : 1 < t := by linarith
  have hlt := Real.log_pos ht1
  have ha0 : (0:ℝ) < (A:ℝ)/1000 := by linarith
  have hlA : val lA ≤ Real.log ((A:ℝ)/1000) :=
    logLo_le QL A 1000 (by unfold QL; norm_num) (by norm_num) (by omega)
  have hlA1 : 1 ≤ val lA := by
    have := val_le hDl; unfold val at this ⊢; rw [div_self D_pos.ne'] at this; exact this
  have hepsHi : eps t ≤ val epsHi := by
    unfold eps
    have hnum : Real.log (1 + 1/t) ≤ val (mlogHi 1000 (A + 1000) 6) := by
      have e := log_one_add_inv A 1000 (by omega) (by norm_num)
      have := mlogHi_ge 1000 (A + 1000) 6 (by omega)
      have hmono : Real.log (1 + 1/t) ≤ Real.log (1 + 1/((A:ℝ)/1000)) := by
        apply Real.log_le_log (by positivity)
        have := one_div_le_one_div_of_le ha0 h1; linarith
      push_cast at e this; linarith
    have hden : val lA ≤ Real.log t := hlA.trans (Real.log_le_log ha0 h1)
    have hlA0 : 0 < val lA := by linarith
    calc Real.log (1 + 1/t) / Real.log t ≤ val (mlogHi 1000 (A + 1000) 6) / val lA := by
          apply div_le_div₀ (val_nonneg _) hnum hlA0 hden
      _ ≤ val epsHi := div_le_fdivU _ _ (by
          by_contra h; push_neg at h; have : lA = 0 := by omega
          rw [this] at hlA0; simp [val] at hlA0)
  have hepsLo : val epsLo ≤ eps t := by
    unfold eps
    have hb0 : (0:ℝ) < (B:ℝ)/1000 := by linarith
    have hB1 : 0 < B := Nat.pos_of_ne_zero (fun h => by rw [h] at hb0; simp at hb0)
    have hnum : val (mlogLo 1000 (B + 1000) 6) ≤ Real.log (1 + 1/t) := by
      have e := log_one_add_inv B 1000 hB1 (by norm_num)
      have := mlogLo_le 1000 (B + 1000) 6 (by omega)
      have hmono : Real.log (1 + 1/((B:ℝ)/1000)) ≤ Real.log (1 + 1/t) := by
        have hbpos : 0 < 1/((B:ℝ)/1000) := div_pos one_pos hb0
        apply Real.log_le_log (by linarith)
        have := one_div_le_one_div_of_le (by linarith) h2.le; linarith
      push_cast at e this; linarith
    have hden : Real.log t ≤ val (logHi QL B 1000) :=
      (Real.log_le_log (by linarith) h2.le).trans
        (logHi_ge QL B 1000 (by unfold QL; norm_num) (by norm_num) hB1)
    calc val epsLo ≤ val (mlogLo 1000 (B + 1000) 6) / val (logHi QL B 1000) := fdivL_le_div _ _
      _ ≤ Real.log (1 + 1/t) / Real.log t := by
          have h1t : 0 ≤ 1/t := by positivity
          apply div_le_div₀ (Real.log_nonneg (by linarith)) hnum hlt hden
  have hG : val (GN epsLo a0) ≤ Gf 8 t := GN_le epsLo a0 hB0 t ht1 hf1 hepsLo
  -- the term eps (t - θ)
  have hbU : t ≤ val (fdivU B 1000) := by
    have := val_fdivU B 1000 (by norm_num); push_cast at this; linarith
  have hterm : eps t * (t - Chebyshev.theta t) ≤ val (fmulU epsHi (fdivU B 1000 - th)) := by
    have he0 := eps_nonneg t ht1
    have hd : t - Chebyshev.theta t ≤ val (fdivU B 1000 - th) :=
      le_trans (by linarith) (val_sub_le _ _)
    refine le_trans ?_ (val_fmulU _ _)
    rcases le_total 0 (t - Chebyshev.theta t) with hpos | hneg
    · exact mul_le_mul hepsHi hd hpos (val_nonneg _)
    · have : eps t * (t - Chebyshev.theta t) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos he0 hneg
      have : 0 ≤ val epsHi * val (fdivU B 1000 - th) := mul_nonneg (val_nonneg _) (val_nonneg _)
      linarith
  -- log log
  have hDpos : 0 < D := by unfold D; norm_num
  have hll : val (logLo QL lA D) ≤ Real.log (Real.log t) := by
    have := logLo_le QL lA D (by unfold QL; norm_num) hDpos hDl
    have hlA0 : 0 < val lA := by linarith
    have e : ((lA:ℝ) / D) = val lA := rfl
    rw [e] at this
    exact this.trans (Real.log_le_log hlA0 (hlA.trans (Real.log_le_log ha0 h1)))
  have hgam := GAM_le
  have hmain' : val (fmulU epsHi (fdivU B 1000 - th)) + val ML <
      val GAM + val (logLo QL lA D) + val (GN epsLo a0) := by
    rw [← val_add, ← val_add, ← val_add]; exact val_lt hmain
  have key : Real.log ((ArithmeticFunction.sigma 1 n : ℝ) / n)
      < Real.eulerMascheroniConstant + Real.log (Real.log t) := by linarith
  have hlt2 : 0 < Real.log t := Real.log_pos (by linarith)
  have hs0 : (0:ℝ) < (ArithmeticFunction.sigma 1 n : ℕ) := by
    exact_mod_cast ArithmeticFunction.sigma_pos 1 n (by omega)
  have := Real.exp_lt_exp.mpr key
  rw [Real.exp_log (div_pos hs0 hn0), Real.exp_add, Real.exp_log hlt2] at this
  rw [div_lt_iff₀ hn0] at this
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

-- ===== PubFin2 =====

set_option autoImplicit false

namespace RobinFix

def finList1 : List (ℕ × ℕ) := [
  (487000, 491000),
  (491000, 499000),
  (499000, 503000),
  (503000, 509000),
  (509000, 521000),
  (521000, 523000),
  (523000, 537500),
  (537500, 541000),
  (541000, 547000),
  (547000, 557000),
  (557000, 563000),
  (563000, 569000),
  (569000, 571000),
  (571000, 577000),
  (577000, 587000),
  (587000, 593000),
  (593000, 599000),
  (599000, 601000),
  (601000, 607000),
  (607000, 613000),
  (613000, 617000),
  (617000, 619000),
  (619000, 631000),
  (631000, 641000),
  (641000, 643000),
  (643000, 647000),
  (647000, 653000),
  (653000, 659000),
  (659000, 661000),
  (661000, 673000),
  (673000, 677000),
  (677000, 683000),
  (683000, 691000),
  (691000, 701000),
  (701000, 709000),
  (709000, 719000),
  (719000, 727000),
  (727000, 733000),
  (733000, 739000),
  (739000, 743000),
  (743000, 751000),
  (751000, 757000),
  (757000, 761000),
  (761000, 769000),
  (769000, 773000),
  (773000, 787000),
  (787000, 797000),
  (797000, 809000),
  (809000, 811000),
  (811000, 821000),
  (821000, 823000),
  (823000, 827000),
  (827000, 829000),
  (829000, 839000),
  (839000, 853000),
  (853000, 857000),
  (857000, 859000),
  (859000, 863000),
  (863000, 877000),
  (877000, 881000),
  (881000, 883000),
  (883000, 887000),
  (887000, 907000),
  (907000, 911000),
  (911000, 919000),
  (919000, 929000),
  (929000, 937000),
  (937000, 941000),
  (941000, 947000),
  (947000, 953000),
  (953000, 967000),
  (967000, 971000),
  (971000, 977000),
  (977000, 983000),
  (983000, 991000),
  (991000, 997000),
  (997000, 1009000)]

lemma finList1_chain : chainOK finList1 487000 1009000 = true := by decide +kernel

lemma finList1_ok : finList1.all (fun p => finchk p.1 p.2) = true := by decide +kernel

end RobinFix

namespace RobinRHParts

theorem robin_logrange_487_1009 : ∀ n : ℕ, (487:ℝ) ≤ Real.log n → Real.log n < 1009 →
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by
  intro n h1 h2
  obtain ⟨p, hp, hp1, hp2⟩ := RobinFix.cover RobinFix.finList1 487000 1009000 RobinFix.finList1_chain 1000
    (by norm_num) (Real.log n) (by norm_num; linarith) (by norm_num; linarith)
  exact RobinFix.finchk_sound p.1 p.2 (List.all_eq_true.mp RobinFix.finList1_ok p hp) n hp1 hp2

end RobinRHParts

theorem solution :
    ∀ n : ℕ, (487:ℝ) ≤ Real.log n → Real.log n < 1009 →
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) :=
  RobinRHParts.robin_logrange_487_1009
