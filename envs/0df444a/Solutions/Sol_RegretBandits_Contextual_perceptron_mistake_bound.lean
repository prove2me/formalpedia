-- Prove2me | solution 1 for RegretBandits.Contextual.perceptron_mistake_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T07:58:53.803635+00:00
-- url     : https://prove2.me/submissions/e2bc1fa5-c67c-4b76-8465-5c2c8ccbb559

import Mathlib
import Definitions.Def_RegretBandits_Contextual_Multiclass

set_option autoImplicit false

namespace PercAB726537

open RegretBandits.Contextual

/-- Frobenius inner product. -/
def ip {K d : ℕ} (U W : Matrix (Fin K) (Fin d) ℝ) : ℝ := ∑ i, ∑ j, U i j * W i j

/-- Squared Frobenius norm. -/
def sq {K d : ℕ} (W : Matrix (Fin K) (Fin d) ℝ) : ℝ := ∑ i, ∑ j, W i j ^ 2

lemma sq_nonneg' {K d : ℕ} (W : Matrix (Fin K) (Fin d) ℝ) : 0 ≤ sq W := by
  unfold sq
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))

lemma mulVec_apply' {K d : ℕ} (U : Matrix (Fin K) (Fin d) ℝ) (v : Fin d → ℝ) (i : Fin K) :
    (Matrix.mulVec U v) i = ∑ j, U i j * v j := by
  simp [Matrix.mulVec, dotProduct]

lemma ip_of {K d : ℕ} (U : Matrix (Fin K) (Fin d) ℝ) (v : Fin d → ℝ) (c : Fin K → ℝ) :
    ip U (Matrix.of (fun i j => v j * c i)) = ∑ i, c i * (Matrix.mulVec U v) i := by
  unfold ip
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mulVec_apply', Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Matrix.of_apply]
  ring

lemma sq_of {K d : ℕ} (v : Fin d → ℝ) (c : Fin K → ℝ) :
    sq (Matrix.of (fun i j => v j * c i) : Matrix (Fin K) (Fin d) ℝ)
      = sqNorm v * ∑ i, c i ^ 2 := by
  unfold sq sqNorm
  rw [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Matrix.of_apply]
  ring

lemma sq_add {K d : ℕ} (W X : Matrix (Fin K) (Fin d) ℝ) :
    sq (W + X) = sq W + 2 * ip W X + sq X := by
  unfold sq ip
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Matrix.add_apply]
  ring

lemma ip_add {K d : ℕ} (U W X : Matrix (Fin K) (Fin d) ℝ) :
    ip U (W + X) = ip U W + ip U X := by
  unfold ip
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Matrix.add_apply]
  ring

lemma ip_zero {K d : ℕ} (U : Matrix (Fin K) (Fin d) ℝ) : ip U 0 = 0 := by
  simp [ip]

lemma sq_zero' {K d : ℕ} : sq (0 : Matrix (Fin K) (Fin d) ℝ) = 0 := by
  simp [sq]

lemma sum_delta {K : ℕ} (a b : Fin K) (w : Fin K → ℝ) :
    ∑ i, ((if a = i then (1:ℝ) else 0) - (if b = i then 1 else 0)) * w i = w a - w b := by
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma sum_delta_sq {K : ℕ} (a b : Fin K) :
    ∑ i, ((if a = i then (1:ℝ) else 0) - (if b = i then 1 else 0)) ^ 2
      = if b ≠ a then 2 else 0 := by
  by_cases h : b = a
  · subst h; simp
  · have : ∀ i, ((if a = i then (1:ℝ) else 0) - (if b = i then 1 else 0)) ^ 2
        = (if a = i then 1 else 0) + (if b = i then 1 else 0) := by
      intro i
      by_cases ha : a = i <;> by_cases hb : b = i
      · exact absurd (hb.trans ha.symm) h
      all_goals simp [ha, hb]
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      ne_eq, h, not_false_eq_true]
    norm_num

lemma W_succ {K d : ℕ} (sel : (Fin K → ℝ) → Fin K) (x : ℕ → Fin d → ℝ) (y : ℕ → Fin K)
    (t : ℕ) :
    perceptronW sel x y (t + 1) = perceptronW sel x y t +
      Matrix.of (fun i j => x t j * ((if y t = i then 1 else 0) -
        (if perceptronPred sel x y t = i then 1 else 0))) := by
  rfl

lemma sq_bound {K d : ℕ} (sel : (Fin K → ℝ) → Fin K) (hsel : IsArgmaxSelector sel)
    (x : ℕ → Fin d → ℝ) (y : ℕ → Fin K) (hx : ∀ t, sqNorm (x t) = 1) (n : ℕ) :
    sq (perceptronW sel x y n) ≤ 2 * perceptronMistakes sel x y n := by
  induction n with
  | zero => simp [perceptronW, perceptronMistakes, sq_zero']
  | succ t ih =>
    rw [W_succ, sq_add, ip_of, sq_of, sum_delta, sum_delta_sq, hx t]
    have hle : (Matrix.mulVec (perceptronW sel x y t) (x t)) (y t) ≤
        (Matrix.mulVec (perceptronW sel x y t) (x t)) (perceptronPred sel x y t) :=
      hsel _ _
    unfold perceptronMistakes at ih ⊢
    rw [Finset.sum_range_succ]
    split_ifs <;> nlinarith

lemma hinge_ge {K d : ℕ} (U : Matrix (Fin K) (Fin d) ℝ) (v : Fin d → ℝ) (a b : Fin K)
    (h : b ≠ a) :
    1 - hingeLoss U v a ≤ (Matrix.mulVec U v) a - (Matrix.mulVec U v) b := by
  unfold hingeLoss
  have hb : (Matrix.mulVec U v) b ≤ ⨆ i : {i : Fin K // i ≠ a}, (Matrix.mulVec U v) i :=
    le_ciSup (f := fun i : {i : Fin K // i ≠ a} => (Matrix.mulVec U v) i)
      (Set.finite_range _).bddAbove ⟨b, h⟩
  have := le_max_right (0:ℝ)
    (1 - (Matrix.mulVec U v) a + ⨆ i : {i : Fin K // i ≠ a}, (Matrix.mulVec U v) i)
  linarith

lemma hinge_nonneg {K d : ℕ} (U : Matrix (Fin K) (Fin d) ℝ) (v : Fin d → ℝ) (a : Fin K) :
    0 ≤ hingeLoss U v a := le_max_left _ _

lemma ip_bound {K d : ℕ} (sel : (Fin K → ℝ) → Fin K)
    (x : ℕ → Fin d → ℝ) (y : ℕ → Fin K) (U : Matrix (Fin K) (Fin d) ℝ) (n : ℕ) :
    perceptronMistakes sel x y n - cumHinge n x y U ≤ ip U (perceptronW sel x y n) := by
  induction n with
  | zero => simp [perceptronW, perceptronMistakes, cumHinge, ip_zero]
  | succ t ih =>
    rw [W_succ, ip_add, ip_of, sum_delta]
    unfold perceptronMistakes cumHinge at ih ⊢
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have h0 := hinge_nonneg U (x t) (y t)
    split_ifs with hm
    · have := hinge_ge U (x t) (y t) (perceptronPred sel x y t) hm
      linarith
    · push_neg at hm
      rw [hm]
      linarith

lemma cs {K d : ℕ} (U W : Matrix (Fin K) (Fin d) ℝ) :
    ip U W ≤ frobNorm U * Real.sqrt (sq W) := by
  have key : ip U W ^ 2 ≤ (∑ i, ∑ j, U i j ^ 2) * sq W := by
    unfold ip sq
    simp only [← Fintype.sum_prod_type']
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  unfold frobNorm
  rw [← Real.sqrt_mul (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
    (fun j _ => sq_nonneg (U i j))))]
  exact le_trans (le_abs_self _) (Real.abs_le_sqrt key)

lemma final_ineq (M L a : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L) (ha : 0 ≤ a)
    (h : M - L ≤ a * Real.sqrt (2 * M)) :
    M ≤ L + 2 * a ^ 2 + a * Real.sqrt (2 * L) := by
  set q := Real.sqrt (2 * M) with hq
  set r := Real.sqrt (2 * L) with hr
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = 2 * M := Real.sq_sqrt (by linarith)
  have hr2 : r ^ 2 = 2 * L := Real.sq_sqrt (by linarith)
  by_contra hc
  push_neg at hc
  -- a q > 2a² + a r, so q > 2a + r
  have h1 : a * q > 2 * a ^ 2 + a * r := by linarith
  have hapos : 0 < a := by
    rcases ha.lt_or_eq with h' | h'
    · exact h'
    · subst h'; nlinarith
  have h2 : q > 2 * a + r := by
    by_contra h3; push_neg at h3; nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h2.le hapos.le]

end PercAB726537

open PercAB726537 in
open RegretBandits.Contextual in
theorem solution {K d : ℕ} (hK : 2 ≤ K)
    (sel : (Fin K → ℝ) → Fin K) (hsel : IsArgmaxSelector sel)
    (x : ℕ → Fin d → ℝ) (y : ℕ → Fin K) (hx : ∀ t, sqNorm (x t) = 1)
    (n : ℕ) (hn : 1 ≤ n) (U : Matrix (Fin K) (Fin d) ℝ) :
    perceptronMistakes sel x y n ≤
      cumHinge n x y U + 2 * frobNorm U ^ 2 +
        frobNorm U * Real.sqrt (2 * n * avgHinge n x y U) := by
  have hn' : (n : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have havg : 2 * (n : ℝ) * avgHinge n x y U = 2 * cumHinge n x y U := by
    unfold avgHinge
    field_simp
  rw [havg]
  have hM : 0 ≤ perceptronMistakes sel x y n := by
    unfold perceptronMistakes
    exact Finset.sum_nonneg (fun t _ => by split_ifs <;> norm_num)
  have hL : 0 ≤ cumHinge n x y U := by
    unfold cumHinge
    exact Finset.sum_nonneg (fun t _ => hinge_nonneg _ _ _)
  have ha : 0 ≤ frobNorm U := Real.sqrt_nonneg _
  apply final_ineq _ _ _ hM hL ha
  calc perceptronMistakes sel x y n - cumHinge n x y U
      ≤ ip U (perceptronW sel x y n) := ip_bound sel x y U n
    _ ≤ frobNorm U * Real.sqrt (sq (perceptronW sel x y n)) := cs _ _
    _ ≤ frobNorm U * Real.sqrt (2 * perceptronMistakes sel x y n) := by
        apply mul_le_mul_of_nonneg_left _ ha
        exact Real.sqrt_le_sqrt (sq_bound sel hsel x y hx n)
