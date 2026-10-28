-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P39.randomRankSandwich
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T09:28:24.158315+00:00
-- url     : https://prove2.me/submissions/95b7c087-a5e0-4e3f-865a-86009c7afcb7

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P39


namespace RRS201

open Real Filter Topology

/-- 2φ(y) series. -/
lemma phi_hasSum {y : ℝ} (hy : |y| < 1) :
    HasSum (fun n : ℕ => (1 / (((n:ℝ) + 1) * (2 * n + 1))) * (y ^ 2) ^ (n + 1))
      ((1 + y) * log (1 + y) + (1 - y) * log (1 - y)) := by
  have hy2 : |y ^ 2| < 1 := by
    rw [abs_pow]; nlinarith [abs_nonneg y]
  have h1 := Real.hasSum_pow_div_log_of_abs_lt_one hy2
  have h2 := (Real.hasSum_log_sub_log_of_abs_lt_one hy).mul_left y
  have h3 := h2.sub h1
  have e : (1 + y) * log (1 + y) + (1 - y) * log (1 - y)
      = y * (log (1 + y) - log (1 - y)) - (-log (1 - y ^ 2)) := by
    have hp : 0 < 1 + y := by linarith [neg_abs_le y]
    have hm : 0 < 1 - y := by linarith [le_abs_self y]
    have : 1 - y ^ 2 = (1 + y) * (1 - y) := by ring
    rw [this, Real.log_mul hp.ne' hm.ne']; ring
  have hf : (fun n : ℕ => (1 / (((n:ℝ) + 1) * (2 * n + 1))) * (y ^ 2) ^ (n + 1)) =
      (fun b : ℕ => y * (2 * (1 / (2 * (b:ℝ) + 1)) * y ^ (2 * b + 1)) - (y ^ 2) ^ (b + 1) / (b + 1)) := by
    funext n
    have hn : ((n:ℝ) + 1) ≠ 0 := by positivity
    have hn2 : (2 * (n:ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  rw [e, hf]; exact h3

lemma phi_le_log_two {y : ℝ} (hy : |y| < 1) :
    (1 + y) * log (1 + y) + (1 - y) * log (1 - y) ≤ 2 * log 2 := by
  have hp : 0 < 1 + y := by linarith [neg_abs_le y]
  have hm : 0 < 1 - y := by linarith [le_abs_self y]
  have := Real.binEntropy_nonneg (p := (1 - y) / 2) (by linarith) (by linarith)
  rw [Real.binEntropy] at this
  have e1 : 1 - (1 - y) / 2 = (1 + y) / 2 := by ring
  rw [e1, Real.log_inv, Real.log_inv, Real.log_div hm.ne' two_ne_zero,
    Real.log_div hp.ne' two_ne_zero] at this
  nlinarith

lemma c_nonneg (n : ℕ) : 0 ≤ (1 / (((n:ℝ) + 1) * (2 * n + 1))) := by positivity

lemma partial_le (N : ℕ) :
    ∑ n ∈ Finset.range N, (1 / (((n:ℝ) + 1) * (2 * n + 1))) ≤ 2 * log 2 := by
  -- limit t → 1⁻ of partial sums with t = y^2
  have hcont : Continuous fun t : ℝ =>
      ∑ n ∈ Finset.range N, (1 / (((n:ℝ) + 1) * (2 * n + 1))) * t ^ (n + 1) := by
    fun_prop
  have hlim : Tendsto (fun t : ℝ =>
      ∑ n ∈ Finset.range N, (1 / (((n:ℝ) + 1) * (2 * n + 1))) * t ^ (n + 1))
      (𝓝[<] 1) (𝓝 (∑ n ∈ Finset.range N, (1 / (((n:ℝ) + 1) * (2 * n + 1))))) := by
    have := (hcont.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Iio 1))
    simpa using this
  refine le_of_tendsto hlim ?_
  have hmem : Set.Ioo (0:ℝ) 1 ∈ 𝓝[<] (1:ℝ) := Ioo_mem_nhdsLT (by norm_num)
  filter_upwards [hmem] with t ht
  obtain ⟨ht0, ht1⟩ := ht
  set y := Real.sqrt t
  have hyt : y ^ 2 = t := Real.sq_sqrt ht0.le
  have hy : |y| < 1 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg t)]
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt ht0.le ht1
  have hs := phi_hasSum hy
  rw [hyt] at hs
  calc _ ≤ ((1 + y) * log (1 + y) + (1 - y) * log (1 - y)) :=
        sum_le_hasSum _ (fun n _ => mul_nonneg (c_nonneg n) (pow_nonneg ht0.le _)) hs
    _ ≤ 2 * log 2 := phi_le_log_two hy

lemma phi_le {y : ℝ} (hy : |y| < 1) :
    (1 + y) * log (1 + y) + (1 - y) * log (1 - y) ≤ 2 * log 2 * y ^ 2 := by
  have hsumm : Summable (fun n : ℕ => (1 / (((n:ℝ) + 1) * (2 * n + 1)))) :=
    summable_of_sum_range_le (fun n => c_nonneg n) partial_le
  have htsum : ∑' n : ℕ, (1 / (((n:ℝ) + 1) * (2 * n + 1))) ≤ 2 * log 2 :=
    hsumm.tsum_le_of_sum_range_le partial_le
  have hs := phi_hasSum hy
  have ht0 : 0 ≤ y ^ 2 := sq_nonneg y
  have ht1 : y ^ 2 ≤ 1 := by
    have : |y| ^ 2 ≤ 1 := by nlinarith [abs_nonneg y]
    simpa [sq_abs] using this
  rw [← hs.tsum_eq]
  calc ∑' n : ℕ, (1 / (((n:ℝ) + 1) * (2 * n + 1))) * (y ^ 2) ^ (n + 1)
      ≤ ∑' n : ℕ, (1 / (((n:ℝ) + 1) * (2 * n + 1))) * y ^ 2 := by
        refine hs.summable.tsum_le_tsum (fun n => ?_) (hsumm.mul_right _)
        refine mul_le_mul_of_nonneg_left ?_ (c_nonneg n)
        rw [pow_succ]
        exact mul_le_of_le_one_left ht0 (pow_le_one₀ ht0 ht1)
    _ = (∑' n : ℕ, (1 / (((n:ℝ) + 1) * (2 * n + 1)))) * y ^ 2 := hsumm.tsum_mul_right _
    _ ≤ 2 * log 2 * y ^ 2 := mul_le_mul_of_nonneg_right htsum ht0

/-- binary entropy lower bound -/
lemma binEnt_ge {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    4 * log 2 * (x * (1 - x)) ≤ -(x * log x) - (1 - x) * log (1 - x) := by
  rcases eq_or_lt_of_le hx0 with h | h
  · subst h; simp
  rcases eq_or_lt_of_le hx1 with h' | h'
  · subst h'; simp
  have hy : |1 - 2 * x| < 1 := by rw [abs_lt]; constructor <;> linarith
  have := phi_le hy
  have e1 : 1 + (1 - 2 * x) = 2 * (1 - x) := by ring
  have e2 : 1 - (1 - 2 * x) = 2 * x := by ring
  rw [e1, e2, Real.log_mul two_ne_zero (by linarith), Real.log_mul two_ne_zero h.ne'] at this
  nlinarith

/-- pair form: a,b ≥ 0. -/
lemma pair_ge {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    log 2 * (a + b - (a - b) ^ 2 / (a + b)) ≤
      a * (log (a + b) - log a) + b * (log (a + b) - log b) := by
  rcases eq_or_lt_of_le (add_nonneg ha hb) with h | h
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    subst ha0 hb0; simp
  set s := a + b with hs
  have hx := binEnt_ge (x := a / s) (div_nonneg ha h.le) (by rw [div_le_one h]; linarith)
  have e1 : 1 - a / s = b / s := by field_simp; linarith
  rw [e1] at hx
  have key : a + b - (a - b) ^ 2 / (a + b) = s * (4 * (a / s * (b / s))) := by
    rw [← hs]; field_simp; ring
  rw [key]
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · subst ha0
    have : b = s := by linarith
    rw [← this]; simp
  rcases eq_or_lt_of_le hb with hb0 | hb0
  · subst hb0
    have : a = s := by linarith
    rw [← this]; simp
  rw [Real.log_div ha0.ne' h.ne', Real.log_div hb0.ne' h.ne'] at hx
  have : s * (-(a / s * (log a - log s)) - b / s * (log b - log s)) =
      a * (log s - log a) + b * (log s - log b) := by field_simp; ring
  nlinarith [mul_le_mul_of_nonneg_left hx h.le]

end RRS201


namespace RRS201

lemma core_id (M u N v s : ℝ) (hN : N ≠ 0) (h1 : N + s * v ≠ 0) (h2 : N - s * v ≠ 0) :
    (M + s * u) ^ 2 / (N + s * v) + (M - s * u) ^ 2 / (N - s * v) =
      2 * (M ^ 2 / N) + 2 * s ^ 2 * ((u * N - M * v) ^ 2 / (N * ((N + s * v) * (N - s * v)))) := by
  field_simp
  ring

lemma core (M u N v s : ℝ) (hN : 0 < N - v) (hN' : 0 < N + v) (hs : s ^ 2 ≤ 1) :
    (M + s * u) ^ 2 / (N + s * v) + (M - s * u) ^ 2 / (N - s * v) ≤
      s ^ 2 * ((M + u) ^ 2 / (N + v) + (M - u) ^ 2 / (N - v)) + 2 * (1 - s ^ 2) * (M ^ 2 / N) := by
  have hN0 : 0 < N := by linarith
  have hsv : |s * v| < N := by
    rw [abs_mul]
    have : |s| ≤ 1 := by
      have : |s| ^ 2 ≤ 1 := by simpa [sq_abs] using hs
      nlinarith [abs_nonneg s]
    have hv : |v| < N := by rw [abs_lt]; constructor <;> linarith
    calc |s| * |v| ≤ 1 * |v| := mul_le_mul_of_nonneg_right this (abs_nonneg v)
      _ < N := by simpa using hv
  have hp : 0 < N + s * v := by linarith [neg_abs_le (s * v)]
  have hm : 0 < N - s * v := by linarith [le_abs_self (s * v)]
  have e1 := core_id M u N v s hN0.ne' hp.ne' hm.ne'
  have e2 := core_id M u N v 1 hN0.ne' (by linarith) (by linarith)
  simp only [one_mul, one_pow] at e2
  rw [e1, e2]
  have hW : 0 ≤ (u * N - M * v) ^ 2 := sq_nonneg _
  have key : (u * N - M * v) ^ 2 / (N * ((N + s * v) * (N - s * v))) ≤
      (u * N - M * v) ^ 2 / (N * ((N + v) * (N - v))) := by
    apply div_le_div_of_nonneg_left hW (by positivity)
    apply mul_le_mul_of_nonneg_left _ hN0.le
    nlinarith [sq_nonneg v]
  nlinarith [mul_le_mul_of_nonneg_left key (sq_nonneg s)]

/-- per-coordinate hybrid inequality -/
lemma hyb_pt (d0 d1 σ0 σ1 x : ℝ) (h0 : |d0| ≤ σ0) (h1 : |d1| ≤ σ1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ((1 - x) * d0 + x * d1) ^ 2 / ((1 - x) * σ0 + x * σ1) +
      ((1 - (1 - x)) * d0 + (1 - x) * d1) ^ 2 / ((1 - (1 - x)) * σ0 + (1 - x) * σ1) ≤
    (1 - 4 * x * (1 - x)) * (d0 ^ 2 / σ0 + d1 ^ 2 / σ1) +
      2 * (4 * x * (1 - x)) * (((d0 + d1) / 2) ^ 2 / ((σ0 + σ1) / 2)) := by
  have hσ0 : 0 ≤ σ0 := le_trans (abs_nonneg _) h0
  have hσ1 : 0 ≤ σ1 := le_trans (abs_nonneg _) h1
  rcases eq_or_lt_of_le hσ0 with e0 | p0
  · subst e0
    have : d0 = 0 := abs_nonpos_iff.mp h0
    subst this
    have hF : ∀ y : ℝ, ((1 - y) * 0 + y * d1) ^ 2 / ((1 - y) * 0 + y * σ1) = y * (d1 ^ 2 / σ1) := by
      intro y
      rcases eq_or_ne y 0 with hy | hy
      · subst hy; simp
      simp only [mul_zero, zero_add]
      rcases eq_or_ne σ1 0 with hs | hs
      · simp [hs]
      · field_simp
    have h1' := hF x
    have h2' := hF (1 - x)
    have h3' : ((0 + d1) / 2) ^ 2 / ((0 + σ1) / 2) = (1/2) * (d1 ^ 2 / σ1) := by
      rcases eq_or_ne σ1 0 with hs | hs
      · simp [hs]
      · field_simp; ring
    simp only [mul_zero, zero_add] at h1' h2'
    simp only [mul_zero, zero_add, zero_div, h1', h2', h3']
    simp only [zero_add] at h3'
    rw [h3']
    ring_nf; exact le_rfl
  rcases eq_or_lt_of_le hσ1 with e1 | p1
  · subst e1
    have : d1 = 0 := abs_nonpos_iff.mp h1
    subst this
    have hF : ∀ y : ℝ, ((1 - y) * d0 + y * 0) ^ 2 / ((1 - y) * σ0 + y * 0) = (1 - y) * (d0 ^ 2 / σ0) := by
      intro y
      rcases eq_or_ne (1 - y) 0 with hy | hy
      · rw [hy]; simp
      simp only [mul_zero, add_zero]
      rcases eq_or_ne σ0 0 with hs | hs
      · simp [hs]
      · field_simp
    have h1' := hF x
    have h2' := hF (1 - x)
    have h3' : ((d0 + 0) / 2) ^ 2 / ((σ0 + 0) / 2) = (1/2) * (d0 ^ 2 / σ0) := by
      simp only [add_zero]; field_simp
    simp only [mul_zero, add_zero] at h1' h2' h3'
    simp only [mul_zero, add_zero, h1', h2', h3', div_zero]
    ring_nf; exact le_rfl
  -- nondegenerate
  have := core ((d0 + d1) / 2) ((d1 - d0) / 2) ((σ0 + σ1) / 2) ((σ1 - σ0) / 2) (2 * x - 1)
    (by linarith) (by linarith) (by nlinarith)
  have a1 : (1 - x) * d0 + x * d1 = (d0 + d1) / 2 + (2 * x - 1) * ((d1 - d0) / 2) := by ring
  have a2 : (1 - x) * σ0 + x * σ1 = (σ0 + σ1) / 2 + (2 * x - 1) * ((σ1 - σ0) / 2) := by ring
  have a3 : (1 - (1 - x)) * d0 + (1 - x) * d1 = (d0 + d1) / 2 - (2 * x - 1) * ((d1 - d0) / 2) := by ring
  have a4 : (1 - (1 - x)) * σ0 + (1 - x) * σ1 = (σ0 + σ1) / 2 - (2 * x - 1) * ((σ1 - σ0) / 2) := by ring
  have a5 : (d0 + d1) / 2 + (d1 - d0) / 2 = d1 := by ring
  have a6 : (σ0 + σ1) / 2 + (σ1 - σ0) / 2 = σ1 := by ring
  have a7 : (d0 + d1) / 2 - (d1 - d0) / 2 = d0 := by ring
  have a8 : (σ0 + σ1) / 2 - (σ1 - σ0) / 2 = σ0 := by ring
  rw [a5, a6, a7, a8] at this
  rw [a1, a2, a3, a4]
  have : (1 - 4 * x * (1 - x)) = (2 * x - 1) ^ 2 := by ring
  rw [this]
  nlinarith

/-- summed hybrid inequality on a finite abelian group with involution `e`. -/
lemma hyb_sum {T : Type*} [AddCommGroup T] [Fintype T] (w e : T) (he : e + e = 0)
    (A : T → ℝ) (hA : ∀ t, 0 ≤ A t) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∑ t, ((1 - x) * (A t - A (t + w)) + x * (A (t + e) - A (t + e + w))) ^ 2 /
        ((1 - x) * (A t + A (t + w)) + x * (A (t + e) + A (t + e + w))) ≤
      (1 - 4 * x * (1 - x)) * ∑ t, (A t - A (t + w)) ^ 2 / (A t + A (t + w)) +
      (4 * x * (1 - x)) * ∑ t, ((A t + A (t + e)) / 2 - (A (t + w) + A (t + e + w)) / 2) ^ 2 /
        ((A t + A (t + e)) / 2 + (A (t + w) + A (t + e + w)) / 2) := by
  set F : ℝ → T → ℝ := fun y t => ((1 - y) * (A t - A (t + w)) + y * (A (t + e) - A (t + e + w))) ^ 2 /
        ((1 - y) * (A t + A (t + w)) + y * (A (t + e) + A (t + e + w))) with hF
  have hsym : ∀ y, ∑ t, F y t = ∑ t, F (1 - y) t := by
    intro y
    refine Fintype.sum_equiv (Equiv.addRight e) _ _ (fun t => ?_)
    simp only [hF, Equiv.coe_addRight]
    have h1 : t + e + e = t := by rw [add_assoc, he, add_zero]
    have h2 : t + e + w + e = t + w := by rw [add_right_comm, h1]
    simp only [h1]; rw [sub_sub_cancel]; congr 1 <;> ring
  have hF0 : ∀ t, F 0 t = (A t - A (t + w)) ^ 2 / (A t + A (t + w)) := by
    intro t; simp [hF]
  have hF1 : ∑ t, F 1 t = ∑ t, (A t - A (t + w)) ^ 2 / (A t + A (t + w)) := by
    rw [show (1:ℝ) = 1 - 0 by norm_num, ← hsym 0]
    exact Finset.sum_congr rfl (fun t _ => hF0 t)
  have hpt : ∀ t, F x t + F (1 - x) t ≤ (1 - 4 * x * (1 - x)) * (F 0 t + F 1 t) +
      2 * (4 * x * (1 - x)) * (((A t + A (t + e)) / 2 - (A (t + w) + A (t + e + w)) / 2) ^ 2 /
        ((A t + A (t + e)) / 2 + (A (t + w) + A (t + e + w)) / 2)) := by
    intro t
    have := hyb_pt (A t - A (t + w)) (A (t + e) - A (t + e + w)) (A t + A (t + w))
      (A (t + e) + A (t + e + w)) x
      (by rw [abs_le]; constructor <;> linarith [hA t, hA (t + w)])
      (by rw [abs_le]; constructor <;> linarith [hA (t + e), hA (t + e + w)]) hx0 hx1
    simp only [hF]
    convert this using 3
    all_goals first | (simp; done) | (ring_nf; done) | (field_simp; ring)
  have hsum := Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => hpt t)
  rw [Finset.sum_add_distrib, ← hsym x, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_add_distrib, hF1] at hsum
  rw [show ∑ t, F 0 t = ∑ t, (A t - A (t + w)) ^ 2 / (A t + A (t + w)) from
    Finset.sum_congr rfl (fun t _ => hF0 t)] at hsum
  change ∑ t, F x t ≤ _
  linarith

end RRS201


open QAlgorithms.Papers.Independent.Information100.P39

namespace RRS201

attribute [local instance] Classical.propDecidable

variable {m : ℕ}

lemma zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x; decide

lemma zmod2_sum (f : ZMod 2 → ℝ) : ∑ x, f x = f 0 + f 1 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from rfl]
  simp

lemma binaryLaw_nonneg {p : Fin m → ℝ} (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) (b : Bits m) :
    0 ≤ binaryLaw p b := by
  unfold binaryLaw
  refine Finset.prod_nonneg (fun a _ => ?_)
  split_ifs <;> linarith [hp a]

lemma binaryLaw_eq (p : Fin m → ℝ) (b : Bits m) :
    binaryLaw p b = ∏ a, (fun a (x : ZMod 2) => if x = 1 then p a else 1 - p a) a (b a) := rfl

lemma sum_binaryLaw (p : Fin m → ℝ) : ∑ b, binaryLaw p b = 1 := by
  have h := Fintype.prod_sum (fun a (x : ZMod 2) => if x = 1 then p a else 1 - p a)
  have h2 : ∏ a, ∑ x : ZMod 2, (if x = 1 then p a else 1 - p a) = 1 := by
    refine Finset.prod_eq_one (fun a _ => ?_)
    rw [zmod2_sum]; simp
  rw [h] at h2
  unfold binaryLaw
  convert h2 using 1

/-- L0: sums against the quotient law. -/
lemma sum_quot (p : Fin m → ℝ) (K : Submodule F2 (Bits m)) (F : Bits m ⧸ K → ℝ) :
    ∑ c, quotientLaw p K c * F c = ∑ b, binaryLaw p b * F (K.mkQ b) := by
  unfold quotientLaw pushLaw
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

lemma sum_quotientLaw (p : Fin m → ℝ) (K : Submodule F2 (Bits m)) :
    ∑ c, quotientLaw p K c = 1 := by
  have := sum_quot p K (fun _ => 1)
  simp only [mul_one] at this
  rw [this, sum_binaryLaw]

lemma quotientLaw_nonneg {p : Fin m → ℝ} (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1)
    (K : Submodule F2 (Bits m)) (c) : 0 ≤ quotientLaw p K c := by
  unfold quotientLaw pushLaw
  refine Finset.sum_nonneg (fun b _ => ?_)
  split_ifs
  · exact binaryLaw_nonneg hp b
  · exact le_rfl

lemma quotientLaw_mk (p : Fin m → ℝ) (K : Submodule F2 (Bits m)) (x : Bits m) :
    quotientLaw p K (K.mkQ x) = ∑ b, if b - x ∈ K then binaryLaw p b else 0 := by
  unfold quotientLaw pushLaw
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [Submodule.mkQ_apply, Submodule.Quotient.eq]

/-! ### affine dependence on one coordinate -/

lemma prod_split_update (f : Fin m → ℝ → ℝ) (p : Fin m → ℝ) (j : Fin m) (y : ℝ) :
    ∏ a, f a (Function.update p j y a) = f j y * ∏ a ∈ Finset.univ.erase j, f a (p a) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl (fun a ha => ?_)
  rw [Function.update_of_ne (Finset.ne_of_mem_erase ha)]

lemma prod_split (f : Fin m → ℝ → ℝ) (p : Fin m → ℝ) (j : Fin m) :
    ∏ a, f a (p a) = f j (p j) * ∏ a ∈ Finset.univ.erase j, f a (p a) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]

lemma binaryLaw_affine (p : Fin m → ℝ) (j : Fin m) (b : Bits m) :
    binaryLaw p b = (1 - p j) * binaryLaw (Function.update p j 0) b +
      p j * binaryLaw (Function.update p j 1) b := by
  have h := fun y => prod_split_update (fun a (z : ℝ) => if b a = 1 then z else 1 - z) p j y
  have h' := prod_split (fun a (z : ℝ) => if b a = 1 then z else 1 - z) p j
  unfold binaryLaw
  beta_reduce at h h'
  rw [h 0, h 1, h']
  split_ifs <;> ring

lemma single_add_self (j : Fin m) : (Pi.single j (1 : F2) : Bits m) + Pi.single j 1 = 0 := by
  funext a
  by_cases h : a = j
  · subst h; simp; decide
  · simp [h]

lemma binaryLaw_shift (p : Fin m → ℝ) (j : Fin m) (b : Bits m) :
    binaryLaw (Function.update p j 1) b =
      binaryLaw (Function.update p j 0) (b + Pi.single j 1) := by
  unfold binaryLaw
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  congr 1
  · simp only [Function.update_self, Pi.add_apply, Pi.single_eq_same]
    rcases zmod2_cases (b j) with h | h <;> rw [h] <;> simp
  · refine Finset.prod_congr rfl (fun a ha => ?_)
    have hne := Finset.ne_of_mem_erase ha
    simp [Function.update_of_ne hne, Pi.single_eq_of_ne hne]

lemma quotientLaw_affine (p : Fin m → ℝ) (j : Fin m) (K : Submodule F2 (Bits m)) (t) :
    quotientLaw p K t = (1 - p j) * quotientLaw (Function.update p j 0) K t +
      p j * quotientLaw (Function.update p j 1) K t := by
  unfold quotientLaw pushLaw
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  split_ifs
  · exact binaryLaw_affine p j b
  · ring

lemma quotientLaw_shift (p : Fin m → ℝ) (j : Fin m) (K : Submodule F2 (Bits m)) (t) :
    quotientLaw (Function.update p j 1) K t =
      quotientLaw (Function.update p j 0) K (t + K.mkQ (Pi.single j 1)) := by
  unfold quotientLaw pushLaw
  refine Fintype.sum_equiv (Equiv.addRight (Pi.single j (1 : F2))) _ _ (fun b => ?_)
  simp only [Equiv.coe_addRight, map_add]
  rw [binaryLaw_shift]
  congr 1
  apply propext
  constructor
  · intro h; rw [h]
  · intro h
    have := congrArg (· + K.mkQ (Pi.single j 1)) h
    simp only [add_assoc, ← map_add, single_add_self, map_zero, add_zero] at this
    exact this

lemma erasedLaw_affine (p : Fin m → ℝ) (j : Fin m) (g : Finset (Fin m)) :
    erasedLaw p g = (1 - 4 * p j * (1 - p j)) * erasedLaw (Function.update p j 0) g +
      (4 * p j * (1 - p j)) * erasedLaw (Function.update p j (1/2)) g := by
  have h := fun y => prod_split_update
    (fun a (z : ℝ) => if a ∈ g then 4 * z * (1 - z) else 1 - 4 * z * (1 - z)) p j y
  have h' := prod_split
    (fun a (z : ℝ) => if a ∈ g then 4 * z * (1 - z) else 1 - 4 * z * (1 - z)) p j
  unfold erasedLaw
  beta_reduce at h h'
  rw [h 0, h (1/2), h']
  split_ifs <;> ring

lemma erasedLaw_nonneg {p : Fin m → ℝ} (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) (g : Finset (Fin m)) :
    0 ≤ erasedLaw p g := by
  unfold erasedLaw
  refine Finset.prod_nonneg (fun a _ => ?_)
  have h1 := hp a
  split_ifs
  · nlinarith
  · nlinarith [sq_nonneg (2 * p a - 1)]

lemma sum_erasedLaw (p : Fin m → ℝ) : ∑ g, erasedLaw p g = 1 := by
  have := Fintype.prod_add (fun a => 4 * p a * (1 - p a)) (fun a => 1 - 4 * p a * (1 - p a))
  simp only [add_sub_cancel, Finset.prod_const_one] at this
  rw [this]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  unfold erasedLaw
  rw [Finset.prod_ite]
  congr 1
  · congr 1; ext a; simp
  · congr 1; ext a; simp

end RRS201



namespace RRS201

attribute [local instance] Classical.propDecidable

variable {m : ℕ}


lemma mem_supported_iff (g : Finset (Fin m)) (x : Bits m) :
    x ∈ supported g ↔ ∀ a, a ∉ g → x a = 0 := by
  constructor
  · intro h
    unfold supported at h
    induction h using Submodule.span_induction with
    | mem y hy => exact hy
    | zero => intro a _; rfl
    | add y z _ _ hy hz => intro a ha; simp [hy a ha, hz a ha]
    | smul c y _ hy => intro a ha; simp [hy a ha]
  · intro h; exact Submodule.subset_span h

lemma mem_sup_span_iff {KT : Submodule F2 (Bits m)} {v y : Bits m} :
    y ∈ KT ⊔ Submodule.span F2 {v} ↔ y ∈ KT ∨ y - v ∈ KT := by
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨k, hk, z, hz, rfl⟩
    rw [Submodule.mem_span_singleton] at hz
    obtain ⟨c, rfl⟩ := hz
    rcases zmod2_cases c with h | h <;> subst h
    · left; simpa using hk
    · right; simpa using hk
  · rintro (h | h)
    · exact ⟨y, h, 0, Submodule.zero_mem _, by simp⟩
    · exact ⟨y - v, h, v, Submodule.mem_span_singleton_self v, by simp⟩

lemma finrank_map_mkQ (K S : Submodule F2 (Bits m)) :
    Module.finrank F2 (S.map K.mkQ) + Module.finrank F2 (S ⊓ K : Submodule F2 (Bits m)) =
      Module.finrank F2 S := by
  have h := LinearMap.finrank_range_add_finrank_ker (K.mkQ.comp S.subtype)
  have h1 : LinearMap.range (K.mkQ.comp S.subtype) = S.map K.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have h2 : LinearMap.ker (K.mkQ.comp S.subtype) = K.comap S.subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  rw [h1, h2] at h
  have h3 : Module.finrank F2 (K.comap S.subtype) = Module.finrank F2 (S ⊓ K : Submodule F2 (Bits m)) := by
    rw [← Submodule.map_comap_subtype]
    exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective S.subtype
      S.injective_subtype _))
  rw [h3] at h
  exact h

lemma kappa_formula {KT KC : Submodule F2 (Bits m)} (hK : KT ≤ KC) (g : Finset (Fin m)) :
    kappa KT KC g =
      Module.finrank F2 ((supported g).map KT.mkQ) -
      Module.finrank F2 ((supported g).map KC.mkQ) ∧
    Module.finrank F2 ((supported g).map KC.mkQ) ≤ Module.finrank F2 ((supported g).map KT.mkQ) := by
  unfold kappa
  have e1 := finrank_map_mkQ KT (KC ⊓ supported g)
  have e2 := finrank_map_mkQ KT (supported g)
  have e3 := finrank_map_mkQ KC (supported g)
  have hi : (KC ⊓ supported g ⊓ KT : Submodule F2 (Bits m)) = supported g ⊓ KT := by
    apply le_antisymm
    · exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
    · exact le_inf (le_inf (inf_le_right.trans hK) inf_le_left) inf_le_right
  have hc : (KC ⊓ supported g : Submodule F2 (Bits m)) = supported g ⊓ KC := inf_comm _ _
  rw [hi] at e1
  rw [hc] at e1
  have m1 : Module.finrank F2 (supported g ⊓ KT : Submodule F2 (Bits m)) ≤
      Module.finrank F2 (supported g ⊓ KC : Submodule F2 (Bits m)) :=
    Submodule.finrank_mono (inf_le_inf_left _ hK)
  rw [hc]
  constructor <;> omega

lemma kappa_self (K : Submodule F2 (Bits m)) (g : Finset (Fin m)) : kappa K K g = 0 := by
  unfold kappa
  rw [Submodule.finrank_eq_zero, Submodule.eq_bot_iff]
  rintro x ⟨y, hy, rfl⟩
  simpa using hy.1

lemma kappa_codim1 {KT : Submodule F2 (Bits m)} {v : Bits m} (g : Finset (Fin m)) :
    kappa KT (KT ⊔ Submodule.span F2 {v}) g =
      if (KT ⊔ Submodule.span F2 {v}) ⊓ supported g ≤ KT then 0 else 1 := by
  unfold kappa
  set M := ((KT ⊔ Submodule.span F2 {v}) ⊓ supported g).map KT.mkQ
  have hle : M ≤ Submodule.span F2 {KT.mkQ v} := by
    rintro _ ⟨y, hy, rfl⟩
    rcases mem_sup_span_iff.mp hy.1 with h | h
    · rw [show KT.mkQ y = 0 from (Submodule.Quotient.mk_eq_zero KT).mpr h]
      exact Submodule.zero_mem _
    · have : KT.mkQ y = KT.mkQ v := (Submodule.Quotient.eq KT).mpr h
      rw [this]; exact Submodule.mem_span_singleton_self _
  have h1 : Module.finrank F2 M ≤ 1 := by
    have := Submodule.finrank_mono hle
    have h2 : Module.finrank F2 (Submodule.span F2 {KT.mkQ v}) ≤ 1 := by
      by_cases hw : KT.mkQ v = 0
      · rw [hw, Submodule.span_singleton_eq_bot.mpr rfl, finrank_bot]; omega
      · rw [finrank_span_singleton hw]
    omega
  split_ifs with h
  · rw [Submodule.finrank_eq_zero, Submodule.eq_bot_iff]
    rintro _ ⟨y, hy, rfl⟩
    simpa using h hy
  · have : Module.finrank F2 M ≠ 0 := by
      rw [Ne, Submodule.finrank_eq_zero, Submodule.eq_bot_iff]
      intro hM
      apply h
      intro y hy
      have := hM (KT.mkQ y) ⟨y, hy, rfl⟩
      simpa using this
    omega

lemma dual_apply_eq (f : Module.Dual F2 (Bits m)) (x : Bits m) :
    f x = dotProduct (fun a => f (fun j => if a = j then 1 else 0)) x := by
  rw [LinearMap.pi_apply_eq_sum_univ f x, dotProduct]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [smul_eq_mul, mul_comm]

lemma dual_char {KT : Submodule F2 (Bits m)} {v : Bits m} (hv : v ∉ KT) (g : Finset (Fin m)) :
    (∃ ψ : Bits m, (∀ a, ψ a ≠ 0 → a ∈ gᶜ) ∧ (∀ k ∈ KT, dotProduct ψ k = 0) ∧
      dotProduct ψ v = 1) ↔ (KT ⊔ Submodule.span F2 {v}) ⊓ supported g ≤ KT := by
  constructor
  · rintro ⟨ψ, hψg, hψK, hψv⟩ x ⟨hxC, hxS⟩
    by_contra hx
    have hxv : x - v ∈ KT := (mem_sup_span_iff.mp hxC).resolve_left hx
    have h1 : dotProduct ψ x = 1 := by
      have := hψK _ hxv
      rw [dotProduct_sub, hψv, sub_eq_zero] at this
      exact this
    have h0 : dotProduct ψ x = 0 := by
      rw [dotProduct]
      refine Finset.sum_eq_zero (fun a _ => ?_)
      by_cases ha : a ∈ g
      · have : ψ a = 0 := by
          by_contra hne
          have := hψg a hne
          simp [ha] at this
        simp [this]
      · simp [(mem_supported_iff g x).mp hxS a ha]
    rw [h1] at h0
    exact one_ne_zero h0
  · intro h
    have hvW : v ∉ KT ⊔ supported g := by
      intro hv'
      rw [Submodule.mem_sup] at hv'
      obtain ⟨k, hk, s, hs, hks⟩ := hv'
      have hsC : s ∈ KT ⊔ Submodule.span F2 {v} := by
        rw [mem_sup_span_iff]; right
        have : s - v = -k := by rw [← hks]; abel
        rw [this]; exact KT.neg_mem hk
      have := h ⟨hsC, hs⟩
      apply hv
      rw [← hks]; exact KT.add_mem hk this
    obtain ⟨f, hfv, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hvW inferInstance
    have hfz : ∀ x ∈ KT ⊔ supported g, f x = 0 := by
      intro x hx
      exact (Submodule.eq_bot_iff _).mp hfW (f x) ⟨x, hx, rfl⟩
    refine ⟨fun a => f (fun j => if a = j then 1 else 0), ?_, ?_, ?_⟩
    · intro a ha
      by_contra hag
      simp only [Finset.mem_compl, not_not] at hag
      apply ha
      apply hfz
      apply Submodule.mem_sup_right
      rw [mem_supported_iff]
      intro b hb
      have : a ≠ b := fun e => hb (e ▸ hag)
      simp [this]
    · intro k hk
      rw [← dual_apply_eq]
      exact hfz k (Submodule.mem_sup_left hk)
    · rw [← dual_apply_eq]
      rcases zmod2_cases (f v) with h0 | h1
      · exact absurd h0 hfv
      · exact h1

end RRS201

namespace RRS201

attribute [local instance] Classical.propDecidable

variable {m : ℕ}

open Real

lemma entropy_one {A : Type*} [Fintype A] (q : A → ℝ) :
    entropy 1 q = -∑ a, q a * Real.log (q a) := by
  simp [entropy]

lemma entropy_two {A : Type*} [Fintype A] (q : A → ℝ) :
    entropy 2 q = -Real.log (∑ a, q a ^ 2) := by
  have h1 : (2 : Order) ≠ ⊤ := by decide
  have h2 : (2 : Order).untopD 0 = 2 := rfl
  simp only [entropy, h1, h2, if_false]
  norm_num
  ring

lemma sq_div_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : (x - y) ^ 2 / (x + y) ≤ x + y := by
  rcases eq_or_lt_of_le (add_nonneg hx hy) with h | h
  · rw [← h]; simp
  · rw [div_le_iff₀ h]; nlinarith

lemma pair_sum {T : Type*} [AddCommGroup T] [Fintype T] (w : T) (hw : w + w = 0) (a : T → ℝ)
    (ha : ∀ t, 0 ≤ a t) (hsum : ∑ t, a t = 1) :
    log 2 * (1 - (1/2) * ∑ t, (a t - a (t + w)) ^ 2 / (a t + a (t + w))) ≤
      ∑ t, a t * (log (a t + a (t + w)) - log (a t)) := by
  have hsw : ∑ t, a (t + w) = 1 := by
    rw [← hsum]; exact Fintype.sum_equiv (Equiv.addRight w) _ _ (fun t => rfl)
  have hS : ∑ t, a t * (log (a t + a (t + w)) - log (a t)) =
      ∑ t, a (t + w) * (log (a t + a (t + w)) - log (a (t + w))) := by
    refine Fintype.sum_equiv (Equiv.addRight w) _ _ (fun t => ?_)
    simp only [Equiv.coe_addRight, add_assoc, hw, add_zero]
    rw [add_comm (a (t + w)) (a t)]
  have hpt : ∀ t, log 2 * (a t + a (t + w) - (a t - a (t + w)) ^ 2 / (a t + a (t + w))) ≤
      a t * (log (a t + a (t + w)) - log (a t)) +
        a (t + w) * (log (a t + a (t + w)) - log (a (t + w))) :=
    fun t => pair_ge (ha t) (ha (t + w))
  have hsum2 := Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => hpt t)
  rw [Finset.sum_add_distrib, ← hS, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, hsum, hsw] at hsum2
  linarith

section codim1

variable (KT : Submodule F2 (Bits m)) (v : Bits m)

lemma qC_pt (p : Fin m → ℝ) (hv : v ∉ KT) (x : Bits m) :
    quotientLaw p (KT ⊔ Submodule.span F2 {v}) ((KT ⊔ Submodule.span F2 {v}).mkQ x) =
      quotientLaw p KT (KT.mkQ x) + quotientLaw p KT (KT.mkQ x + KT.mkQ v) := by
  rw [← map_add, quotientLaw_mk, quotientLaw_mk, quotientLaw_mk, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have e : b - (x + v) = b - x - v := by abel
  rw [e]
  by_cases h1 : b - x ∈ KT
  · have h2 : b - x - v ∉ KT := by
      intro h2; apply hv
      have := KT.sub_mem h1 h2
      simpa using this
    have h3 : b - x ∈ KT ⊔ Submodule.span F2 {v} := mem_sup_span_iff.mpr (Or.inl h1)
    simp [h1, h2, h3]
  · by_cases h2 : b - x - v ∈ KT
    · have h3 : b - x ∈ KT ⊔ Submodule.span F2 {v} := mem_sup_span_iff.mpr (Or.inr h2)
      simp [h1, h2, h3]
    · have h3 : b - x ∉ KT ⊔ Submodule.span F2 {v} := by
        rw [mem_sup_span_iff]; tauto
      simp [h1, h2, h3]

lemma deficit1_eq (p : Fin m → ℝ) (hv : v ∉ KT) :
    linearDeficit p KT (KT ⊔ Submodule.span F2 {v}) 1 =
      ∑ t, quotientLaw p KT t * (log (quotientLaw p KT t + quotientLaw p KT (t + KT.mkQ v)) -
        log (quotientLaw p KT t)) := by
  unfold linearDeficit
  rw [entropy_one, entropy_one]
  have hC := sum_quot p (KT ⊔ Submodule.span F2 {v})
    (fun c => log (quotientLaw p (KT ⊔ Submodule.span F2 {v}) c))
  have hT := sum_quot p KT (fun t => log (quotientLaw p KT t + quotientLaw p KT (t + KT.mkQ v)))
  beta_reduce at hC hT
  have : ∑ b, binaryLaw p b * log (quotientLaw p (KT ⊔ Submodule.span F2 {v})
      ((KT ⊔ Submodule.span F2 {v}).mkQ b)) =
      ∑ b, binaryLaw p b * log (quotientLaw p KT (KT.mkQ b) +
        quotientLaw p KT (KT.mkQ b + KT.mkQ v)) := by
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [qC_pt KT v p hv]
  rw [hC, this, ← hT]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- the χ²-type quantity -/
noncomputable def Vf (p : Fin m → ℝ) : ℝ :=
  ∑ t, (quotientLaw p KT t - quotientLaw p KT (t + KT.mkQ v)) ^ 2 /
    (quotientLaw p KT t + quotientLaw p KT (t + KT.mkQ v))

noncomputable def Dd (p : Fin m → ℝ) : ℝ :=
  ∑ g, erasedLaw p g * (if (KT ⊔ Submodule.span F2 {v}) ⊓ supported g ≤ KT then 1 else 0)

lemma Vf_le_two (p : Fin m → ℝ) (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) : Vf KT v p ≤ 2 := by
  unfold Vf
  calc _ ≤ ∑ t, (quotientLaw p KT t + quotientLaw p KT (t + KT.mkQ v)) :=
        Finset.sum_le_sum (fun t _ => sq_div_le (quotientLaw_nonneg hp _ _)
          (quotientLaw_nonneg hp _ _))
    _ = 2 := by
        rw [Finset.sum_add_distrib, sum_quotientLaw]
        have : ∑ t, quotientLaw p KT (t + KT.mkQ v) = ∑ t, quotientLaw p KT t :=
          Fintype.sum_equiv (Equiv.addRight (KT.mkQ v)) _ _ (fun t => rfl)
        rw [this, sum_quotientLaw]; norm_num

lemma Vf_nonneg (p : Fin m → ℝ) (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) : 0 ≤ Vf KT v p := by
  unfold Vf
  exact Finset.sum_nonneg (fun t _ => div_nonneg (sq_nonneg _)
    (add_nonneg (quotientLaw_nonneg hp _ _) (quotientLaw_nonneg hp _ _)))

lemma Dd_nonneg (p : Fin m → ℝ) (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) : 0 ≤ Dd KT v p := by
  unfold Dd
  refine Finset.sum_nonneg (fun g _ => mul_nonneg (erasedLaw_nonneg hp g) ?_)
  split_ifs <;> norm_num

lemma Dd_affine (p : Fin m → ℝ) (j : Fin m) :
    Dd KT v p = (1 - 4 * p j * (1 - p j)) * Dd KT v (Function.update p j 0) +
      (4 * p j * (1 - p j)) * Dd KT v (Function.update p j (1/2)) := by
  unfold Dd
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [erasedLaw_affine p j g]
  ring

lemma upd_bounds {p : Fin m → ℝ} (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) (j : Fin m) (y : ℝ)
    (hy : 0 ≤ y ∧ y ≤ 1) : ∀ a, 0 ≤ Function.update p j y a ∧ Function.update p j y a ≤ 1 := by
  intro a
  by_cases h : a = j
  · subst h; simpa using hy
  · rw [Function.update_of_ne h]; exact hp a

lemma hyb_step (p : Fin m → ℝ) (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) (j : Fin m) :
    Vf KT v p ≤ (1 - 4 * p j * (1 - p j)) * Vf KT v (Function.update p j 0) +
      (4 * p j * (1 - p j)) * Vf KT v (Function.update p j (1/2)) := by
  set A := quotientLaw (Function.update p j 0) KT with hAdef
  set e := KT.mkQ (Pi.single j (1 : F2)) with hedef
  set w := KT.mkQ v with hwdef
  have he : e + e = 0 := by rw [hedef, ← map_add, single_add_self, map_zero]
  have hA : ∀ t, 0 ≤ A t := fun t => quotientLaw_nonneg (upd_bounds hp j 0 (by norm_num)) _ _
  have hap : ∀ t, quotientLaw p KT t = (1 - p j) * A t + p j * A (t + e) := by
    intro t; rw [quotientLaw_affine p j KT t, quotientLaw_shift]
  have hah : ∀ t, quotientLaw (Function.update p j (1/2)) KT t = (A t + A (t + e)) / 2 := by
    intro t
    rw [quotientLaw_affine _ j KT t]
    simp only [Function.update_idem, Function.update_self]
    rw [quotientLaw_shift]
    ring
  have H := hyb_sum w e he A hA (p j) (hp j).1 (hp j).2
  have L : Vf KT v p = ∑ t, ((1 - p j) * (A t - A (t + w)) + p j * (A (t + e) - A (t + e + w))) ^ 2 /
        ((1 - p j) * (A t + A (t + w)) + p j * (A (t + e) + A (t + e + w))) := by
    unfold Vf
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [hap, hap, add_right_comm t w e]
    congr 1 <;> ring
  have R1 : Vf KT v (Function.update p j 0) = ∑ t, (A t - A (t + w)) ^ 2 / (A t + A (t + w)) := rfl
  have R2 : Vf KT v (Function.update p j (1/2)) =
      ∑ t, ((A t + A (t + e)) / 2 - (A (t + w) + A (t + e + w)) / 2) ^ 2 /
        ((A t + A (t + e)) / 2 + (A (t + w) + A (t + e + w)) / 2) := by
    unfold Vf
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [hah, hah, add_right_comm t w e]
  rw [L, R1, R2]
  exact H

lemma base_case (p : Fin m → ℝ) (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1)
    (hpure : ∀ a, p a = 0 ∨ p a = 1/2) : Vf KT v p ≤ 2 * Dd KT v p := by
  set G := Finset.univ.filter (fun a => p a = 1/2) with hG
  by_cases hc : (KT ⊔ Submodule.span F2 {v}) ⊓ supported G ≤ KT
  · have h1 : erasedLaw p G = 1 := by
      unfold erasedLaw
      refine Finset.prod_eq_one (fun a _ => ?_)
      by_cases ha : a ∈ G
      · have : p a = 1/2 := (Finset.mem_filter.mp ha).2
        rw [if_pos ha, this]; norm_num
      · have : p a = 0 := by
          rcases hpure a with h | h
          · exact h
          · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ a, h⟩) ha
        rw [if_neg ha, this]; norm_num
    have h2 : 1 ≤ Dd KT v p := by
      unfold Dd
      have := Finset.single_le_sum (f := fun g => erasedLaw p g *
        (if (KT ⊔ Submodule.span F2 {v}) ⊓ supported g ≤ KT then (1:ℝ) else 0))
        (fun g _ => mul_nonneg (erasedLaw_nonneg hp g) (by split_ifs <;> norm_num))
        (Finset.mem_univ G)
      simp only [h1, if_pos hc, mul_one] at this
      exact this
    linarith [Vf_le_two KT v p hp]
  · obtain ⟨s, hs, hsT⟩ := SetLike.not_le_iff_exists.mp hc
    have hsw : KT.mkQ s = KT.mkQ v :=
      (Submodule.Quotient.eq KT).mpr ((mem_sup_span_iff.mp hs.1).resolve_left hsT)
    have hsupp := (mem_supported_iff G s).mp hs.2
    have hPs : ∀ b, binaryLaw p (b + s) = binaryLaw p b := by
      intro b
      unfold binaryLaw
      refine Finset.prod_congr rfl (fun a _ => ?_)
      by_cases ha : a ∈ G
      · have : p a = 1/2 := (Finset.mem_filter.mp ha).2
        rw [this]; split_ifs <;> norm_num
      · simp [hsupp a ha]
    have hinv : ∀ t, quotientLaw p KT (t + KT.mkQ v) = quotientLaw p KT t := by
      intro t
      rw [← hsw]
      unfold quotientLaw pushLaw
      refine (Fintype.sum_equiv (Equiv.addRight s) _ _ (fun b => ?_)).symm
      simp only [Equiv.coe_addRight, map_add, hPs]
      congr 1
      apply propext
      constructor
      · intro h; rw [h]
      · intro h; exact add_right_cancel h
    have : Vf KT v p = 0 := by
      unfold Vf
      refine Finset.sum_eq_zero (fun t _ => ?_)
      rw [hinv]; simp
    rw [this]
    linarith [Dd_nonneg KT v p hp]

lemma V_le_D_aux (s : Finset (Fin m)) : ∀ p : Fin m → ℝ, (∀ a, 0 ≤ p a ∧ p a ≤ 1) →
    (∀ a, a ∉ s → p a = 0 ∨ p a = 1/2) → Vf KT v p ≤ 2 * Dd KT v p := by
  induction s using Finset.induction_on with
  | empty =>
    intro p hp hpure
    exact base_case KT v p hp (fun a => hpure a (Finset.notMem_empty a))
  | insert j s hj ih =>
    intro p hp hpure
    have h0 := ih (Function.update p j 0) (upd_bounds hp j 0 (by norm_num)) (by
      intro a ha
      by_cases h : a = j
      · subst h; simp
      · rw [Function.update_of_ne h]
        exact hpure a (by simp [h, ha]))
    have h1 := ih (Function.update p j (1/2)) (upd_bounds hp j (1/2) (by norm_num)) (by
      intro a ha
      by_cases h : a = j
      · subst h; simp
      · rw [Function.update_of_ne h]
        exact hpure a (by simp [h, ha]))
    have hθ0 : 0 ≤ 4 * p j * (1 - p j) := by nlinarith [hp j]
    have hθ1 : 0 ≤ 1 - 4 * p j * (1 - p j) := by nlinarith [sq_nonneg (2 * p j - 1)]
    calc Vf KT v p ≤ (1 - 4 * p j * (1 - p j)) * Vf KT v (Function.update p j 0) +
          (4 * p j * (1 - p j)) * Vf KT v (Function.update p j (1/2)) := hyb_step KT v p hp j
      _ ≤ (1 - 4 * p j * (1 - p j)) * (2 * Dd KT v (Function.update p j 0)) +
          (4 * p j * (1 - p j)) * (2 * Dd KT v (Function.update p j (1/2))) := by
          gcongr
      _ = 2 * Dd KT v p := by rw [Dd_affine KT v p j]; ring

lemma sum_kappa_codim1 (p : Fin m → ℝ) :
    ∑ g, erasedLaw p g * (kappa KT (KT ⊔ Submodule.span F2 {v}) g : ℝ) = 1 - Dd KT v p := by
  unfold Dd
  rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  convert sum_erasedLaw p using 2 with g
  rw [kappa_codim1]
  split_ifs <;> simp

theorem shannon_codim1 (p : Fin m → ℝ) (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) (hv : v ∉ KT) :
    log 2 * ∑ g, erasedLaw p g * (kappa KT (KT ⊔ Submodule.span F2 {v}) g : ℝ) ≤
      linearDeficit p KT (KT ⊔ Submodule.span F2 {v}) 1 := by
  rw [sum_kappa_codim1, deficit1_eq KT v p hv]
  have h2 : (2 : F2) = 0 := by decide
  have hw : KT.mkQ v + KT.mkQ v = 0 := by rw [← map_add, ← two_smul F2 v, h2, zero_smul, map_zero]
  have H := pair_sum (KT.mkQ v) hw (quotientLaw p KT) (quotientLaw_nonneg hp KT)
    (sum_quotientLaw p KT)
  have HV := V_le_D_aux KT v Finset.univ p hp (fun a ha => absurd (Finset.mem_univ a) ha)
  have hl : 0 < log 2 := Real.log_pos (by norm_num)
  change log 2 * (1 - (1/2) * Vf KT v p) ≤ _ at H
  nlinarith

end codim1

end RRS201

namespace RRS201

attribute [local instance] Classical.propDecidable

variable {m : ℕ}

open Real

/-! ### Rényi-2 part -/

def sg (x : F2) : ℝ := if x = 0 then 1 else -1

lemma sg_add (x y : F2) : sg (x + y) = sg x * sg y := by
  unfold sg
  rcases zmod2_cases x with hx | hx <;> rcases zmod2_cases y with hy | hy <;> subst hx hy <;>
    simp <;> decide

lemma sg_sum {ι : Type*} (s : Finset ι) (f : ι → F2) : sg (∑ i ∈ s, f i) = ∏ i ∈ s, sg (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sg]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, sg_add, ih]

noncomputable def lam (p : Fin m → ℝ) (a : Fin m) : ℝ := (1 - 2 * p a) ^ 2

noncomputable def Lam (p : Fin m → ℝ) (ψ : Bits m) : ℝ := ∏ a, if ψ a = 0 then 1 else lam p a

noncomputable def nu (p : Fin m → ℝ) (U : Finset (Fin m)) : ℝ :=
  ∏ a, if a ∈ U then lam p a else 1 - lam p a

noncomputable def cK (K : Submodule F2 (Bits m)) : ℝ := ∑ d : Bits m, if d ∈ K then (1:ℝ) else 0

noncomputable def Wt (p : Fin m → ℝ) (K : Submodule F2 (Bits m)) : ℝ :=
  ∑ ψ, Lam p ψ * (if ∀ k ∈ K, dotProduct ψ k = 0 then 1 else 0)

noncomputable def NK (K : Submodule F2 (Bits m)) (U : Finset (Fin m)) : ℝ :=
  ∑ ψ : Bits m, if (∀ a, a ∉ U → ψ a = 0) ∧ (∀ k ∈ K, dotProduct ψ k = 0) then (1:ℝ) else 0

lemma lam_bounds {p : Fin m → ℝ} (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) (a : Fin m) :
    0 ≤ lam p a ∧ lam p a ≤ 1 := by
  unfold lam
  have := hp a
  constructor
  · positivity
  · nlinarith

lemma Lam_nonneg {p : Fin m → ℝ} (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) (ψ : Bits m) : 0 ≤ Lam p ψ := by
  unfold Lam
  refine Finset.prod_nonneg (fun a _ => ?_)
  split_ifs
  · norm_num
  · exact (lam_bounds hp a).1

lemma nu_nonneg {p : Fin m → ℝ} (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) (U : Finset (Fin m)) :
    0 ≤ nu p U := by
  unfold nu
  refine Finset.prod_nonneg (fun a _ => ?_)
  have := lam_bounds hp a
  split_ifs <;> linarith

lemma nu_split (p : Fin m → ℝ) (t : Finset (Fin m)) :
    nu p t = (∏ a ∈ t, lam p a) * ∏ a ∈ tᶜ, (1 - lam p a) := by
  unfold nu
  rw [Finset.prod_ite]
  congr 2
  · ext a; simp
  · ext a; simp

lemma sum_nu (p : Fin m → ℝ) : ∑ U, nu p U = 1 := by
  have := Fintype.prod_add (fun a => lam p a) (fun a => 1 - lam p a)
  simp only [add_sub_cancel, Finset.prod_const_one] at this
  rw [this]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [nu_split]

/-- collision probability as a sum over pairs -/
lemma coll_eq1 (p : Fin m → ℝ) (K : Submodule F2 (Bits m)) :
    ∑ c, quotientLaw p K c ^ 2 =
      ∑ d : Bits m, if d ∈ K then ∑ b, binaryLaw p b * binaryLaw p (b + d) else 0 := by
  have h := sum_quot p K (fun c => quotientLaw p K c)
  beta_reduce at h
  simp_rw [sq]
  rw [h]
  have h2 : ∀ b : Bits m, binaryLaw p b * quotientLaw p K (K.mkQ b) =
      ∑ d : Bits m, if d ∈ K then binaryLaw p b * binaryLaw p (b + d) else 0 := by
    intro b
    rw [quotientLaw_mk, Finset.mul_sum]
    refine (Fintype.sum_equiv (Equiv.addLeft b) _ _ (fun d => ?_)).symm
    simp only [Equiv.coe_addLeft, add_sub_cancel_left]
    split_ifs <;> simp
  simp_rw [h2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  split_ifs <;> simp

lemma R_prod (p : Fin m → ℝ) (d : Bits m) :
    ∑ b, binaryLaw p b * binaryLaw p (b + d) =
      ∏ a, ∑ x : ZMod 2, (if x = 1 then p a else 1 - p a) *
        (if x + d a = 1 then p a else 1 - p a) := by
  have h := Fintype.prod_sum (fun a (x : ZMod 2) => (if x = 1 then p a else 1 - p a) *
        (if x + d a = 1 then p a else 1 - p a))
  rw [h]
  unfold binaryLaw
  convert rfl using 1
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.prod_mul_distrib]
  rfl

lemma r_char (p : Fin m → ℝ) (a : Fin m) (y : ZMod 2) :
    ∑ x : ZMod 2, (if x = 1 then p a else 1 - p a) * (if x + y = 1 then p a else 1 - p a) =
      (1/2) * ∑ z : ZMod 2, (if z = 0 then 1 else lam p a) * sg (z * y) := by
  rw [zmod2_sum, zmod2_sum]
  unfold lam sg
  rcases zmod2_cases y with h | h <;> subst h <;> simp <;> ring_nf <;> simp <;> ring

lemma R_fourier (p : Fin m → ℝ) (d : Bits m) :
    ∑ b, binaryLaw p b * binaryLaw p (b + d) =
      (1/2) ^ m * ∑ ψ, Lam p ψ * sg (dotProduct ψ d) := by
  rw [R_prod]
  simp_rw [r_char]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl (fun ψ _ => ?_)
  rw [Finset.prod_mul_distrib]
  unfold Lam dotProduct
  rw [sg_sum]

lemma char_sum (K : Submodule F2 (Bits m)) (ψ : Bits m) :
    ∑ d : Bits m, (if d ∈ K then sg (dotProduct ψ d) else 0) =
      if ∀ k ∈ K, dotProduct ψ k = 0 then cK K else 0 := by
  split_ifs with h
  · unfold cK
    refine Finset.sum_congr rfl (fun d _ => ?_)
    split_ifs with hd
    · rw [h d hd]; simp [sg]
    · rfl
  · push_neg at h
    obtain ⟨k, hk, hψk⟩ := h
    have hk1 : dotProduct ψ k = 1 := (zmod2_cases _).resolve_left hψk
    have e := Fintype.sum_equiv (Equiv.addRight k)
        (fun d => if d + k ∈ K then sg (dotProduct ψ (d + k)) else 0)
        (fun d => if d ∈ K then sg (dotProduct ψ d) else 0) (fun d => rfl)
    have : (∑ d : Bits m, (if d ∈ K then sg (dotProduct ψ d) else 0)) =
        -(∑ d : Bits m, (if d ∈ K then sg (dotProduct ψ d) else 0)) := by
      conv_lhs => rw [← e]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun d _ => ?_)
      have hiff : d + k ∈ K ↔ d ∈ K := by
        constructor
        · intro h'; have := K.sub_mem h' hk; simpa using this
        · intro h'; exact K.add_mem h' hk
      by_cases hd : d ∈ K
      · rw [if_pos (hiff.mpr hd), if_pos hd, dotProduct_add, sg_add, hk1]
        simp [sg]
      · rw [if_neg (fun h' => hd (hiff.mp h')), if_neg hd]; simp
    linarith

lemma coll_eq (p : Fin m → ℝ) (K : Submodule F2 (Bits m)) :
    ∑ c, quotientLaw p K c ^ 2 = (1/2) ^ m * cK K * Wt p K := by
  rw [coll_eq1]
  simp_rw [R_fourier]
  have : ∀ d : Bits m, (if d ∈ K then (1/2:ℝ) ^ m * ∑ ψ, Lam p ψ * sg (dotProduct ψ d) else 0) =
      (1/2) ^ m * ∑ ψ, Lam p ψ * (if d ∈ K then sg (dotProduct ψ d) else 0) := by
    intro d; split_ifs <;> simp
  simp_rw [this]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, char_sum]
  unfold Wt
  rw [mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ψ _ => ?_)
  split_ifs <;> ring

lemma cK_pos (K : Submodule F2 (Bits m)) : 1 ≤ cK K := by
  unfold cK
  have := Finset.single_le_sum (f := fun d : Bits m => if d ∈ K then (1:ℝ) else 0)
    (fun d _ => by split_ifs <;> norm_num) (Finset.mem_univ 0)
  simpa [K.zero_mem] using this

lemma Wt_pos {p : Fin m → ℝ} (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) (K : Submodule F2 (Bits m)) :
    1 ≤ Wt p K := by
  unfold Wt
  have := Finset.single_le_sum (f := fun ψ : Bits m =>
    Lam p ψ * (if ∀ k ∈ K, dotProduct ψ k = 0 then (1:ℝ) else 0))
    (fun ψ _ => mul_nonneg (Lam_nonneg hp ψ) (by split_ifs <;> norm_num)) (Finset.mem_univ 0)
  have h0 : Lam p 0 = 1 := by unfold Lam; simp
  simpa [h0, zero_dotProduct] using this

lemma Lam_eq (p : Fin m → ℝ) (ψ : Bits m) :
    Lam p ψ = ∑ U, nu p U * (if ∀ a, a ∉ U → ψ a = 0 then 1 else 0) := by
  have := Fintype.prod_add (fun a => lam p a) (fun a => if ψ a = 0 then 1 - lam p a else 0)
  have e : ∀ a, lam p a + (if ψ a = 0 then 1 - lam p a else 0) = if ψ a = 0 then 1 else lam p a := by
    intro a; split_ifs <;> ring
  simp only [e] at this
  unfold Lam
  rw [this]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Finset.prod_ite_zero, nu_split]
  have hiff : (∀ a ∈ tᶜ, ψ a = 0) ↔ (∀ a, a ∉ t → ψ a = 0) := by simp
  by_cases h : ∀ a, a ∉ t → ψ a = 0
  · rw [if_pos (hiff.mpr h), if_pos h]; ring
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]; ring

lemma Wt_eq (p : Fin m → ℝ) (K : Submodule F2 (Bits m)) :
    Wt p K = ∑ U, nu p U * NK K U := by
  unfold Wt NK
  simp_rw [Lam_eq, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun U _ => Finset.sum_congr rfl (fun ψ _ => ?_))
  split_ifs <;> simp_all

section codim1F

variable (KT : Submodule F2 (Bits m)) (v : Bits m)

noncomputable def dl (U : Finset (Fin m)) : ℝ :=
  if ∃ ψ : Bits m, (∀ a, a ∉ U → ψ a = 0) ∧ (∀ k ∈ KT, dotProduct ψ k = 0) ∧
    dotProduct ψ v = 1 then 1 else 0

lemma perp_C_iff (hv : v ∉ KT) (ψ : Bits m) :
    (∀ k ∈ KT ⊔ Submodule.span F2 {v}, dotProduct ψ k = 0) ↔
      (∀ k ∈ KT, dotProduct ψ k = 0) ∧ dotProduct ψ v = 0 := by
  constructor
  · intro h
    exact ⟨fun k hk => h k (Submodule.mem_sup_left hk),
      h v (Submodule.mem_sup_right (Submodule.mem_span_singleton_self v))⟩
  · rintro ⟨h1, h2⟩ k hk
    rcases mem_sup_span_iff.mp hk with h | h
    · exact h1 k h
    · have := h1 _ h
      rw [dotProduct_sub, h2, sub_zero] at this
      exact this

lemma NK_T_eq (hv : v ∉ KT) (U : Finset (Fin m)) :
    NK KT U = NK (KT ⊔ Submodule.span F2 {v}) U * (1 + dl KT v U) := by
  unfold NK
  have hsplit : ∀ ψ : Bits m,
      (if (∀ a, a ∉ U → ψ a = 0) ∧ (∀ k ∈ KT, dotProduct ψ k = 0) then (1:ℝ) else 0) =
      (if (∀ a, a ∉ U → ψ a = 0) ∧ (∀ k ∈ KT ⊔ Submodule.span F2 {v}, dotProduct ψ k = 0)
        then (1:ℝ) else 0) +
      (if (∀ a, a ∉ U → ψ a = 0) ∧ (∀ k ∈ KT, dotProduct ψ k = 0) ∧ dotProduct ψ v = 1
        then (1:ℝ) else 0) := by
    intro ψ
    simp only [perp_C_iff KT v hv]
    rcases zmod2_cases (dotProduct ψ v) with h | h <;> simp [h]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, mul_add, mul_one]
  congr 1
  unfold dl
  split_ifs with hd
  · obtain ⟨ψ0, h1, h2, h3⟩ := hd
    rw [mul_one]
    refine Fintype.sum_equiv (Equiv.addRight ψ0) _ _ (fun ψ => ?_)
    simp only [Equiv.coe_addRight]
    simp only [perp_C_iff KT v hv]
    have hsupp : (∀ a, a ∉ U → ψ a = 0) ↔ (∀ a, a ∉ U → (ψ + ψ0) a = 0) := by
      constructor
      · intro h a ha; simp [h a ha, h1 a ha]
      · intro h a ha; have := h a ha; simp [h1 a ha] at this; exact this
    have hperp : (∀ k ∈ KT, dotProduct ψ k = 0) ↔ (∀ k ∈ KT, dotProduct (ψ + ψ0) k = 0) := by
      constructor
      · intro h k hk; rw [add_dotProduct, h k hk, h2 k hk, add_zero]
      · intro h k hk; have := h k hk; rwa [add_dotProduct, h2 k hk, add_zero] at this
    have hval : dotProduct ψ v = 1 ↔ dotProduct (ψ + ψ0) v = 0 := by
      rw [add_dotProduct, h3]
      rcases zmod2_cases (dotProduct ψ v) with h | h <;> rw [h] <;> decide
    simp only [hsupp, hperp, hval]
  · rw [mul_zero]
    refine Finset.sum_eq_zero (fun ψ _ => ?_)
    rw [if_neg]
    intro h
    exact hd ⟨ψ, h⟩

lemma dl_nonneg (U : Finset (Fin m)) : 0 ≤ dl KT v U := by
  unfold dl; split_ifs <;> norm_num

lemma dl_le_one (U : Finset (Fin m)) : dl KT v U ≤ 1 := by
  unfold dl; split_ifs <;> norm_num

lemma NK_nonneg (K : Submodule F2 (Bits m)) (U : Finset (Fin m)) : 0 ≤ NK K U := by
  unfold NK; exact Finset.sum_nonneg (fun ψ _ => by split_ifs <;> norm_num)

lemma NK_mono (K : Submodule F2 (Bits m)) : Monotone (NK K) := by
  intro U U' hU
  unfold NK
  refine Finset.sum_le_sum (fun ψ _ => ?_)
  by_cases h : (∀ a, a ∉ U → ψ a = 0) ∧ (∀ k ∈ K, dotProduct ψ k = 0)
  · have h' : (∀ a, a ∉ U' → ψ a = 0) ∧ (∀ k ∈ K, dotProduct ψ k = 0) :=
      ⟨fun a ha => h.1 a (fun hh => ha (hU hh)), h.2⟩
    rw [if_pos h, if_pos h']
  · rw [if_neg h]; split_ifs <;> norm_num

lemma dl_mono : Monotone (dl KT v) := by
  intro U U' hU
  unfold dl
  split_ifs with h h'
  · exact le_rfl
  · exfalso; apply h'
    obtain ⟨ψ, h1, h2, h3⟩ := h
    exact ⟨ψ, fun a ha => h1 a (fun hh => ha (hU hh)), h2, h3⟩
  · norm_num
  · exact le_rfl

lemma nu_logmod (p : Fin m → ℝ) (U U' : Finset (Fin m)) :
    nu p U * nu p U' ≤ nu p (U ⊓ U') * nu p (U ⊔ U') := by
  apply le_of_eq
  unfold nu
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun a _ => ?_)
  simp only [Finset.inf_eq_inter, Finset.sup_eq_union, Finset.mem_inter, Finset.mem_union]
  by_cases h1 : a ∈ U <;> by_cases h2 : a ∈ U' <;> simp [h1, h2] <;> ring

lemma nu_compl (p : Fin m → ℝ) (g : Finset (Fin m)) : nu p gᶜ = erasedLaw p g := by
  unfold nu erasedLaw lam
  refine Finset.prod_congr rfl (fun a _ => ?_)
  by_cases h : a ∈ g
  · simp [h]; ring
  · simp [h]; ring

lemma sum_nu_dl (p : Fin m → ℝ) (hv : v ∉ KT) :
    ∑ U, nu p U * dl KT v U = Dd KT v p := by
  unfold Dd
  refine Fintype.sum_equiv (Equiv.mk compl compl compl_compl compl_compl) _ _ (fun U => ?_)
  simp only [Equiv.coe_fn_mk]
  rw [← nu_compl, compl_compl]
  congr 1
  unfold dl
  have := dual_char hv Uᶜ
  rw [compl_compl] at this
  have hiff : (∃ ψ : Bits m, (∀ a, a ∉ U → ψ a = 0) ∧ (∀ k ∈ KT, dotProduct ψ k = 0) ∧
      dotProduct ψ v = 1) ↔ (∃ ψ : Bits m, (∀ a, ψ a ≠ 0 → a ∈ U) ∧
      (∀ k ∈ KT, dotProduct ψ k = 0) ∧ dotProduct ψ v = 1) := by
    constructor
    · rintro ⟨ψ, h1, h2, h3⟩
      exact ⟨ψ, fun a ha => by by_contra hh; exact ha (h1 a hh), h2, h3⟩
    · rintro ⟨ψ, h1, h2, h3⟩
      exact ⟨ψ, fun a ha => by by_contra hh; exact ha (h1 a hh), h2, h3⟩
  simp only [hiff, this]

theorem renyi_codim1 (p : Fin m → ℝ) (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) (hv : v ∉ KT) :
    linearDeficit p KT (KT ⊔ Submodule.span F2 {v}) 2 ≤
      log 2 * ∑ g, erasedLaw p g * (kappa KT (KT ⊔ Submodule.span F2 {v}) g : ℝ) := by
  set KC := KT ⊔ Submodule.span F2 {v} with hKC
  rw [sum_kappa_codim1]
  unfold linearDeficit
  rw [entropy_two, entropy_two, coll_eq, coll_eq]
  -- cardinalities
  have hcC : cK KC = 2 * cK KT := by
    unfold cK
    have e1 : ∀ d : Bits m, (if d ∈ KC then (1:ℝ) else 0) =
        (if d ∈ KT then 1 else 0) + (if d - v ∈ KT then 1 else 0) := by
      intro d
      rw [hKC]
      by_cases h1 : d ∈ KT
      · have h2 : d - v ∉ KT := by
          intro h2; apply hv; have := KT.sub_mem h1 h2; simpa using this
        rw [if_pos (mem_sup_span_iff.mpr (Or.inl h1)), if_pos h1, if_neg h2]; ring
      · by_cases h2 : d - v ∈ KT
        · rw [if_pos (mem_sup_span_iff.mpr (Or.inr h2)), if_neg h1, if_pos h2]; ring
        · rw [if_neg (fun h => by rcases mem_sup_span_iff.mp h with h | h <;> contradiction),
            if_neg h1, if_neg h2]; ring
    simp_rw [e1]
    rw [Finset.sum_add_distrib]
    have e2 : ∑ d : Bits m, (if d - v ∈ KT then (1:ℝ) else 0) =
        ∑ d : Bits m, (if d ∈ KT then (1:ℝ) else 0) :=
      Fintype.sum_equiv (Equiv.subRight v) _ _ (fun d => rfl)
    rw [e2]; ring
  -- FKG
  have hfkg := fkg (μ := nu p) (f := NK KC) (g := dl KT v) (fun U => nu_nonneg hp U)
    (fun U => NK_nonneg KC U) (fun U => dl_nonneg KT v U) (NK_mono KC) (dl_mono KT v)
    (nu_logmod p)
  rw [sum_nu, one_mul, sum_nu_dl KT v p hv] at hfkg
  have hWT : Wt p KT = Wt p KC + ∑ U, nu p U * (NK KC U * dl KT v U) := by
    rw [Wt_eq, Wt_eq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun U _ => ?_)
    rw [NK_T_eq KT v hv]; ring
  rw [← Wt_eq] at hfkg
  have hD0 : 0 ≤ Dd KT v p := Dd_nonneg KT v p hp
  have hD1 : Dd KT v p ≤ 1 := by
    rw [← sum_nu_dl KT v p hv, ← sum_nu p]
    exact Finset.sum_le_sum (fun U _ => by
      have := nu_nonneg hp U; have := dl_le_one KT v U; nlinarith)
  have hWC := Wt_pos hp KC
  have hcT := cK_pos KT
  have hWT2 : Wt p KC * (1 + Dd KT v p) ≤ Wt p KT := by nlinarith
  have hh : (0:ℝ) < (1/2) ^ m := by positivity
  have hWTpos : 0 < Wt p KT := by nlinarith
  rw [hcC]
  have l1 : log ((1/2) ^ m * (2 * cK KT) * Wt p KC) =
      log ((1/2) ^ m) + log 2 + log (cK KT) + log (Wt p KC) := by
    rw [Real.log_mul (by positivity) (by linarith), Real.log_mul (by positivity) (by linarith),
      Real.log_mul (by norm_num) (by linarith)]
    ring
  have l2 : log ((1/2) ^ m * cK KT * Wt p KT) =
      log ((1/2) ^ m) + log (cK KT) + log (Wt p KT) := by
    rw [Real.log_mul (by positivity) (by linarith), Real.log_mul (by positivity) (by linarith)]
  have l3 : log (Wt p KC) + log (1 + Dd KT v p) ≤ log (Wt p KT) := by
    rw [← Real.log_mul (by linarith) (by linarith)]
    exact Real.log_le_log (by nlinarith) hWT2
  have l4 : Dd KT v p * log 2 ≤ log (1 + Dd KT v p) := by
    have h2 : (1 + 1 : ℝ) ^ Dd KT v p ≤ 1 + Dd KT v p * 1 :=
      rpow_one_add_le_one_add_mul_self (by norm_num) hD0 hD1
    norm_num at h2
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by positivity) h2
  rw [l1, l2]
  nlinarith

end codim1F

end RRS201

namespace RRS201

attribute [local instance] Classical.propDecidable

variable {m : ℕ}

open Real

lemma deficit_add (p : Fin m → ℝ) (K1 K2 K3 : Submodule F2 (Bits m)) (r : Order) :
    linearDeficit p K1 K3 r = linearDeficit p K1 K2 r + linearDeficit p K2 K3 r := by
  unfold linearDeficit; ring

lemma kappa_add {K1 K2 K3 : Submodule F2 (Bits m)} (h12 : K1 ≤ K2) (h23 : K2 ≤ K3)
    (g : Finset (Fin m)) : kappa K1 K3 g = kappa K1 K2 g + kappa K2 K3 g := by
  have a := kappa_formula (h12.trans h23) g
  have b := kappa_formula h12 g
  have c := kappa_formula h23 g
  omega

lemma tele (p : Fin m → ℝ) (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) (KC : Submodule F2 (Bits m)) :
    ∀ n, ∀ KT : Submodule F2 (Bits m), KT ≤ KC →
      Module.finrank F2 KC - Module.finrank F2 KT = n →
      (log 2 * (∑ g : Finset (Fin m), erasedLaw p g * (kappa KT KC g : ℝ)) ≤
        linearDeficit p KT KC 1 ∧
       linearDeficit p KT KC 2 ≤
        log 2 * (∑ g : Finset (Fin m), erasedLaw p g * (kappa KT KC g : ℝ))) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro KT hK hn
  by_cases heq : KT = KC
  · subst heq
    simp [kappa_self, linearDeficit]
  have hlt : KT < KC := lt_of_le_of_ne hK heq
  obtain ⟨v, hvC, hvT⟩ := SetLike.exists_of_lt hlt
  set K' := KT ⊔ Submodule.span F2 {v} with hK'
  have hK'C : K' ≤ KC := sup_le hK ((Submodule.span_singleton_le_iff_mem v KC).mpr hvC)
  have hTK' : KT ≤ K' := le_sup_left
  have hTK'lt : KT < K' := by
    refine lt_of_le_of_ne hTK' (fun h => hvT ?_)
    rw [h]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)
  have hr1 := Submodule.finrank_lt_finrank_of_lt hTK'lt
  have hr2 := Submodule.finrank_mono hK'C
  have hIH := ih (Module.finrank F2 KC - Module.finrank F2 K') (by omega) K' hK'C rfl
  have hS := shannon_codim1 KT v p hp hvT
  have hR := renyi_codim1 KT v p hp hvT
  have hsum : ∑ g : Finset (Fin m), erasedLaw p g * (kappa KT KC g : ℝ) =
      ∑ g : Finset (Fin m), erasedLaw p g * (kappa KT K' g : ℝ) +
      ∑ g : Finset (Fin m), erasedLaw p g * (kappa K' KC g : ℝ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [kappa_add hTK' hK'C g]
    push_cast; ring
  rw [hsum, deficit_add p KT K' KC 1, deficit_add p KT K' KC 2]
  constructor
  · nlinarith [hIH.1]
  · nlinarith [hIH.2]

end RRS201

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P39 in
open scoped Matrix ComplexConjugate in
theorem solution {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1)
    (KT KC : Submodule F2 (Bits m)) (hK : KT ≤ KC) :
    (∀ g, kappa KT KC g =
      Module.finrank F2 ((supported g).map KT.mkQ) -
      Module.finrank F2 ((supported g).map KC.mkQ)) ∧
    Real.log 2 * (∑ g : Finset (Fin m), erasedLaw p g * (kappa KT KC g : ℝ)) ≤
      linearDeficit p KT KC 1 ∧
    linearDeficit p KT KC 2 ≤
      Real.log 2 * (∑ g : Finset (Fin m), erasedLaw p g * (kappa KT KC g : ℝ)) := by
  refine ⟨fun g => (RRS201.kappa_formula hK g).1, ?_⟩
  exact RRS201.tele p hp KC _ KT hK rfl

