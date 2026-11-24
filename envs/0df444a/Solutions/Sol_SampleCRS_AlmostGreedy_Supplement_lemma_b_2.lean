-- Prove2me | solution 1 for SampleCRS.AlmostGreedy.Supplement.lemma_b_2
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T00:58:09.966285+00:00
-- url     : https://prove2.me/submissions/0f335bac-c4ca-4f28-896a-9b38b425f5c7

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_Supplement_scaling

open SampleCRS.AlmostGreedy.Supplement
open scoped Nat

namespace B2Aux

/-- Poisson mass function as a function of the mean. -/
noncomputable def pp (j : ℕ) (x : ℝ) : ℝ := Real.exp (-x) * x ^ j / (j ! : ℝ)

/-- Poisson probability of a value below n. -/
noncomputable def Qf (n : ℕ) (x : ℝ) : ℝ := ∑ j ∈ Finset.range n, pp j x

/-- Expectation of the minimum of a Poisson variable and k. -/
noncomputable def mm (k : ℕ) (x : ℝ) : ℝ := x * Qf k x + (k : ℝ) * (1 - Qf (k + 1) x)

noncomputable def F1 (n : ℕ) (x : ℝ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) * (1 - Qf (n + 1 + 1) x) / mm (n + 1) x ^ 2

noncomputable def F2 (n : ℕ) (x : ℝ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) * (pp (n + 1) x * mm (n + 1) x - 2 * (1 - Qf (n + 1 + 1) x) * Qf (n + 1) x) /
    mm (n + 1) x ^ 3

lemma pp_pos (j : ℕ) {x : ℝ} (hx : 0 < x) : 0 < pp j x := by
  unfold pp
  positivity

lemma pp_nonneg (j : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ pp j x := by
  unfold pp
  positivity

lemma pp_succ (j : ℕ) (x : ℝ) : ((j : ℝ) + 1) * pp (j + 1) x = x * pp j x := by
  unfold pp
  rw [Nat.factorial_succ]
  have h1 : (j ! : ℝ) ≠ 0 := by positivity
  have h2 : ((j : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  try ring

lemma exp_neg_deriv (x : ℝ) : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
  have h := (hasDerivAt_neg x).exp
  simpa using h

lemma pp_zero_deriv (x : ℝ) : HasDerivAt (pp 0) (-pp 0 x) x := by
  have e : pp 0 = fun y : ℝ => Real.exp (-y) := by
    funext y
    simp [pp]
  have e' : pp 0 x = Real.exp (-x) := by simp [pp]
  rw [e', e]
  exact exp_neg_deriv x

lemma pp_succ_deriv (j : ℕ) (x : ℝ) : HasDerivAt (pp (j + 1)) (pp j x - pp (j + 1) x) x := by
  have h := ((exp_neg_deriv x).mul (hasDerivAt_pow (j + 1) x)).div_const ((j + 1)! : ℝ)
  refine HasDerivAt.congr_deriv (f := pp (j + 1)) h ?_
  unfold pp
  rw [Nat.factorial_succ]
  have h1 : (j ! : ℝ) ≠ 0 := by positivity
  have h2 : ((j : ℝ) + 1) ≠ 0 := by positivity
  simp only [Nat.add_sub_cancel]
  push_cast
  field_simp
  try ring

lemma Qf_deriv (n : ℕ) (x : ℝ) : HasDerivAt (Qf (n + 1)) (-pp n x) x := by
  induction n with
  | zero =>
    have e : Qf (0 + 1) = pp 0 := by
      funext y
      simp [Qf]
    rw [e]
    exact pp_zero_deriv x
  | succ n ih =>
    have e : Qf (n + 1 + 1) = fun y => Qf (n + 1) y + pp (n + 1) y := by
      funext y
      unfold Qf
      rw [Finset.sum_range_succ]
    rw [e]
    refine (ih.add (pp_succ_deriv n x)).congr_deriv ?_
    ring

lemma mm_deriv (n : ℕ) (x : ℝ) : HasDerivAt (mm (n + 1)) (Qf (n + 1) x) x := by
  have h : HasDerivAt (mm (n + 1))
      (1 * Qf (n + 1) x + x * (-pp n x) + ((n + 1 : ℕ) : ℝ) * (0 - -pp (n + 1) x)) x :=
    ((hasDerivAt_id x).mul (Qf_deriv n x)).add
      (((hasDerivAt_const x (1 : ℝ)).sub (Qf_deriv (n + 1) x)).const_mul ((n + 1 : ℕ) : ℝ))
  refine h.congr_deriv ?_
  push_cast
  linear_combination pp_succ n x

lemma F_deriv (n : ℕ) (x : ℝ) (hm : mm (n + 1) x ≠ 0) :
    HasDerivAt (fun y => y / mm (n + 1) y) (F1 n x) x := by
  have h : HasDerivAt (fun y => y / mm (n + 1) y)
      ((1 * mm (n + 1) x - x * Qf (n + 1) x) / mm (n + 1) x ^ 2) x :=
    (hasDerivAt_id x).div (mm_deriv n x) hm
  refine h.congr_deriv ?_
  unfold F1
  congr 1
  unfold mm
  ring

lemma F1_deriv (n : ℕ) (x : ℝ) (hm : mm (n + 1) x ≠ 0) : HasDerivAt (F1 n) (F2 n x) x := by
  have hT : HasDerivAt (fun y => ((n + 1 : ℕ) : ℝ) * (1 - Qf (n + 1 + 1) y))
      (((n + 1 : ℕ) : ℝ) * (0 - -pp (n + 1) x)) x :=
    ((hasDerivAt_const x (1 : ℝ)).sub (Qf_deriv (n + 1) x)).const_mul _
  have hm2 : HasDerivAt (fun y => mm (n + 1) y ^ 2) (2 * mm (n + 1) x * Qf (n + 1) x) x := by
    have h := (mm_deriv n x).pow 2
    refine h.congr_deriv ?_
    norm_num
  have h := hT.div hm2 (pow_ne_zero 2 hm)
  refine HasDerivAt.congr_deriv (f := F1 n) h ?_
  unfold F2
  field_simp
  try ring

lemma hs_pp (x : ℝ) (hx : 0 ≤ x) : HasSum (fun j => pp j x) 1 := by
  have h := ProbabilityTheory.hasSum_one_poissonMeasure (Real.toNNReal x)
  rw [Real.coe_toNNReal x hx] at h
  exact h

lemma tail_hasSum (k : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    HasSum (fun i => pp (i + k + 1) x) (1 - Qf (k + 1) x) :=
  (hasSum_nat_add_iff' (k + 1)).mpr (hs_pp x hx)

lemma tail_nonneg (k : ℕ) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ 1 - Qf (k + 1) x :=
  (tail_hasSum k x hx).nonneg (fun _ => pp_nonneg _ hx)

lemma tail_bound (k : ℕ) (x : ℝ) (hx : 0 ≤ x) (hx2 : x < k + 2) :
    (1 - Qf (k + 1) x) * (1 - x / ((k : ℝ) + 2)) ≤ pp (k + 1) x := by
  have hc : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hr0 : 0 ≤ x / ((k : ℝ) + 2) := by positivity
  have hr1 : x / ((k : ℝ) + 2) < 1 := (div_lt_one hc).mpr hx2
  have hgeo := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (pp (k + 1) x)
  have hle : ∀ i, pp (i + k + 1) x ≤ pp (k + 1) x * (x / ((k : ℝ) + 2)) ^ i := by
    intro i
    have hf : ((k + 1)! : ℝ) * ((k : ℝ) + 2) ^ i ≤ ((i + k + 1)! : ℝ) := by
      have h := Nat.factorial_mul_pow_le_factorial (m := k + 1) (n := i)
      have h' : (k + 1)! * (k + 2) ^ i ≤ (i + k + 1)! := by
        rwa [show k + 1 + i = i + k + 1 by omega] at h
      exact_mod_cast h'
    unfold pp
    rw [div_pow, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    have hE : 0 ≤ Real.exp (-x) * x ^ (k + 1) * x ^ i := by positivity
    calc Real.exp (-x) * x ^ (i + k + 1) * (((k + 1)! : ℝ) * ((k : ℝ) + 2) ^ i)
        = (Real.exp (-x) * x ^ (k + 1) * x ^ i) * (((k + 1)! : ℝ) * ((k : ℝ) + 2) ^ i) := by ring
      _ ≤ (Real.exp (-x) * x ^ (k + 1) * x ^ i) * ((i + k + 1)! : ℝ) :=
          mul_le_mul_of_nonneg_left hf hE
      _ = Real.exp (-x) * x ^ (k + 1) * x ^ i * ((i + k + 1)! : ℝ) := by ring
  have h := hasSum_le hle (tail_hasSum k x hx) hgeo
  have hd : 0 < 1 - x / ((k : ℝ) + 2) := by linarith
  have h' := mul_le_mul_of_nonneg_right h hd.le
  rwa [mul_assoc, inv_mul_cancel₀ hd.ne', mul_one] at h'

lemma pp_le (x : ℝ) : ∀ n j : ℕ, j ≤ n → (n : ℝ) ≤ x → pp j x ≤ pp n x := by
  intro n
  induction n with
  | zero =>
    intro j hj _
    rw [Nat.le_zero.mp hj]
  | succ n ih =>
    intro j hj hx
    push_cast at hx
    have hx0 : 0 ≤ x := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hstep : pp n x ≤ pp (n + 1) x := by
      have h := pp_succ n x
      have hp := pp_nonneg n hx0
      have h3 : ((n : ℝ) + 1) * pp n x ≤ ((n : ℝ) + 1) * pp (n + 1) x := by
        rw [h]
        exact mul_le_mul_of_nonneg_right hx hp
      exact le_of_mul_le_mul_left h3 (by positivity)
    rcases Nat.lt_or_ge j (n + 1) with h | h
    · exact (ih j (by omega) (by linarith)).trans hstep
    · rw [show j = n + 1 by omega]

lemma head_bound (n : ℕ) (x : ℝ) (hx : (n : ℝ) ≤ x) :
    Qf (n + 1) x ≤ ((n : ℝ) + 1) * pp n x := by
  unfold Qf
  have h := Finset.sum_le_card_nsmul (Finset.range (n + 1)) (fun j => pp j x) (pp n x)
    (fun j hj => pp_le x n j (by have := Finset.mem_range.mp hj; omega) hx)
  simpa [nsmul_eq_mul] using h

lemma mm_pos (n : ℕ) (x : ℝ) (hx : 0 < x) : 0 < mm (n + 1) x := by
  unfold mm
  exact add_pos_of_pos_of_nonneg
    (mul_pos hx (Finset.sum_pos (fun j _ => pp_pos j hx) Finset.nonempty_range_add_one))
    (mul_nonneg (Nat.cast_nonneg _) (tail_nonneg (n + 1) x hx.le))

lemma alg (n x Q T p : ℝ) (hn : 1 ≤ n) (hx2 : x ≤ n + 1)
    (hQ0 : 0 ≤ Q) (hT0 : 0 ≤ T)
    (h1 : T * ((n + 3) - x) * (n + 2) ≤ (n + 3) * (x * p))
    (h2 : Q * x ≤ (n + 1) ^ 2 * p) :
    0 ≤ p * (x * Q + (n + 1) * T) - 2 * T * Q := by
  have hU : 0 ≤ T * Q := mul_nonneg hT0 hQ0
  have h3 : 2 * (n + 3) * (n + 1) ≤ (n + 1) * (n + 2) * ((n + 3) - x) + (n + 3) * x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx2) (show (0 : ℝ) ≤ n ^ 2 + 2 * n - 1 by nlinarith),
      sq_nonneg (n + 1)]
  have g1 : (n + 1) * (T * ((n + 3) - x) * (n + 2)) * Q ≤ (n + 1) * ((n + 3) * (x * p)) * Q :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by linarith)) hQ0
  have g2 : (n + 3) * (Q * x) * T ≤ (n + 3) * ((n + 1) ^ 2 * p) * T :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by linarith)) hT0
  have g3 : 0 ≤ T * Q *
      ((n + 1) * (n + 2) * ((n + 3) - x) + (n + 3) * x - 2 * (n + 3) * (n + 1)) :=
    mul_nonneg hU (by linarith)
  have hab : 0 < (n + 3) * (n + 1) := by nlinarith
  have fin : 0 ≤ (n + 3) * (n + 1) * (p * (x * Q + (n + 1) * T) - 2 * T * Q) := by
    nlinarith [g1, g2, g3]
  exact (mul_nonneg_iff_of_pos_left hab).mp fin

lemma key (n : ℕ) (hn : (1 : ℝ) ≤ n) (x : ℝ) (hx1 : (n : ℝ) ≤ x) (hx2 : x ≤ n + 1) :
    0 ≤ pp (n + 1) x * mm (n + 1) x - 2 * (1 - Qf (n + 1 + 1) x) * Qf (n + 1) x := by
  have hx0 : 0 < x := by linarith
  have hQ0 : 0 ≤ Qf (n + 1) x := Finset.sum_nonneg fun j _ => pp_nonneg j hx0.le
  have hT0 : 0 ≤ 1 - Qf (n + 1 + 1) x := tail_nonneg (n + 1) x hx0.le
  have hs1 := pp_succ n x
  have hs2 := pp_succ (n + 1) x
  push_cast at hs2
  have hB1 := tail_bound (n + 1) x hx0.le (by push_cast; linarith)
  have e3 : (((n + 1 : ℕ) : ℝ) + 2) = (n : ℝ) + 3 := by push_cast; ring
  rw [e3] at hB1
  have hB2 := head_bound n x hx1
  have hpos : (0 : ℝ) < ((n : ℝ) + 3) * ((n : ℝ) + 2) := by positivity
  have h1 : (1 - Qf (n + 1 + 1) x) * (((n : ℝ) + 3) - x) * ((n : ℝ) + 2) ≤
      ((n : ℝ) + 3) * (x * pp (n + 1) x) := by
    have h := mul_le_mul_of_nonneg_right hB1 hpos.le
    have e1 : (1 - Qf (n + 1 + 1) x) * (1 - x / ((n : ℝ) + 3)) * (((n : ℝ) + 3) * ((n : ℝ) + 2)) =
        (1 - Qf (n + 1 + 1) x) * (((n : ℝ) + 3) - x) * ((n : ℝ) + 2) := by
      have : ((n : ℝ) + 3) ≠ 0 := by positivity
      field_simp
    have e2 : pp (n + 1 + 1) x * (((n : ℝ) + 3) * ((n : ℝ) + 2)) =
        ((n : ℝ) + 3) * (x * pp (n + 1) x) := by
      linear_combination ((n : ℝ) + 3) * hs2
    rw [e1, e2] at h
    exact h
  have h2 : Qf (n + 1) x * x ≤ ((n : ℝ) + 1) ^ 2 * pp (n + 1) x := by
    have h := mul_le_mul_of_nonneg_right hB2 hx0.le
    have e : ((n : ℝ) + 1) * pp n x * x = ((n : ℝ) + 1) ^ 2 * pp (n + 1) x := by
      linear_combination (-(n : ℝ) - 1) * hs1
    rw [e] at h
    exact h
  have hfin := alg n x (Qf (n + 1) x) (1 - Qf (n + 1 + 1) x) (pp (n + 1) x) hn hx2 hQ0 hT0 h1 h2
  unfold mm
  push_cast
  linarith [hfin]

lemma AR_small (n j : ℕ) (hj : j < n + 1) : StaticProphetSec.AR (n + 1) j = 1 := by
  unfold StaticProphetSec.AR
  refine min_eq_left ?_
  have hj' : (j : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast hj
  have hpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  rw [le_div_iff₀ hpos]
  linarith

lemma AR_big (n i : ℕ) : StaticProphetSec.AR (n + 1) (i + (n + 1)) =
    ((n + 1 : ℕ) : ℝ) / (((i + (n + 1) : ℕ) : ℝ) + 1) := by
  unfold StaticProphetSec.AR
  refine min_eq_right ?_
  have hpos : (0 : ℝ) < ((i + (n + 1) : ℕ) : ℝ) + 1 := by positivity
  rw [div_le_one hpos]
  push_cast
  linarith [Nat.cast_nonneg (α := ℝ) i]

lemma term_big (n i : ℕ) (x : ℝ) (hx : 0 < x) :
    StaticProphetSec.AR (n + 1) (i + (n + 1)) * pp (i + (n + 1)) x =
      ((n + 1 : ℕ) : ℝ) / x * pp (i + (n + 1) + 1) x := by
  have h := pp_succ (i + (n + 1)) x
  have hne : (((i + (n + 1) : ℕ) : ℝ) + 1) ≠ 0 := by positivity
  rw [AR_big, div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_div_iff hne hx.ne']
  linear_combination (-((n + 1 : ℕ) : ℝ)) * h

lemma hasSum_AR (n : ℕ) (x : ℝ) (hx : 0 < x) :
    HasSum (fun j => StaticProphetSec.AR (n + 1) j * pp j x) (mm (n + 1) x / x) := by
  have hT : HasSum (fun i => pp (i + (n + 1) + 1) x) (1 - Qf (n + 1 + 1) x) :=
    tail_hasSum (n + 1) x hx.le
  have htail : HasSum (fun i => StaticProphetSec.AR (n + 1) (i + (n + 1)) * pp (i + (n + 1)) x)
      (((n + 1 : ℕ) : ℝ) / x * (1 - Qf (n + 1 + 1) x)) := by
    have hfe : (fun i => StaticProphetSec.AR (n + 1) (i + (n + 1)) * pp (i + (n + 1)) x) =
        fun i => ((n + 1 : ℕ) : ℝ) / x * pp (i + (n + 1) + 1) x :=
      funext fun i => term_big n i x hx
    rw [hfe]
    exact hT.mul_left _
  have hall := (hasSum_nat_add_iff
    (f := fun j => StaticProphetSec.AR (n + 1) j * pp j x) (n + 1)).mp htail
  have hhead : ∑ j ∈ Finset.range (n + 1), StaticProphetSec.AR (n + 1) j * pp j x =
      Qf (n + 1) x := by
    unfold Qf
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [AR_small n j (Finset.mem_range.mp hj), one_mul]
  rw [hhead] at hall
  have hval : ((n + 1 : ℕ) : ℝ) / x * (1 - Qf (n + 1 + 1) x) + Qf (n + 1) x = mm (n + 1) x / x := by
    unfold mm
    have hx' : x ≠ 0 := hx.ne'
    field_simp
    try ring
  rw [hval] at hall
  exact hall

lemma poisE_eq (n : ℕ) (x : ℝ) (hx : 0 < x) :
    StaticProphetSec.poisE (StaticProphetSec.AR (n + 1)) (Real.toNNReal x) = mm (n + 1) x / x := by
  have hterm : ∀ j, StaticProphetSec.AR (n + 1) j *
      (ProbabilityTheory.poissonMeasure (Real.toNNReal x)).real {j} =
        StaticProphetSec.AR (n + 1) j * pp j x := by
    intro j
    rw [ProbabilityTheory.poissonMeasure_real_singleton, Real.coe_toNNReal x hx.le, pp]
  show ∑' j, StaticProphetSec.AR (n + 1) j *
      (ProbabilityTheory.poissonMeasure (Real.toNNReal x)).real {j} = _
  rw [tsum_congr hterm]
  exact (hasSum_AR n x hx).tsum_eq

end B2Aux

open B2Aux

theorem solution (k : ℕ) (hk : 2 ≤ k) :
    ConvexOn ℝ (Set.Icc ((k : ℝ) - 1) (k : ℝ)) (reciprocalAR k) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD : ∀ x ∈ Set.Icc (((n + 1 : ℕ) : ℝ) - 1) ((n + 1 : ℕ) : ℝ),
      (n : ℝ) ≤ x ∧ x ≤ n + 1 ∧ 0 < x := by
    intro x hx
    have h1 := hx.1
    have h2 := hx.2
    push_cast at h1 h2
    exact ⟨by linarith, by linarith, by linarith⟩
  have hconv : ConvexOn ℝ (Set.Icc (((n + 1 : ℕ) : ℝ) - 1) ((n + 1 : ℕ) : ℝ))
      (fun x => x / mm (n + 1) x) := by
    refine convexOn_of_hasDerivWithinAt2_nonneg (f' := F1 n) (f'' := F2 n) (convex_Icc _ _)
      ?_ ?_ ?_ ?_
    · intro x hx
      exact (F_deriv n x (mm_pos n x (hD x hx).2.2).ne').continuousAt.continuousWithinAt
    · intro x hx
      have hx' := hD x (interior_subset hx)
      exact (F_deriv n x (mm_pos n x hx'.2.2).ne').hasDerivWithinAt
    · intro x hx
      have hx' := hD x (interior_subset hx)
      exact (F1_deriv n x (mm_pos n x hx'.2.2).ne').hasDerivWithinAt
    · intro x hx
      have hx' := hD x (interior_subset hx)
      unfold F2
      exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (key n hnr x hx'.1 hx'.2.1))
        (pow_pos (mm_pos n x hx'.2.2) 3).le
  refine hconv.congr ?_
  intro x hx
  show x / mm (n + 1) x = reciprocalAR (n + 1) x
  unfold reciprocalAR
  rw [poisE_eq n x (hD x hx).2.2, one_div_div]
