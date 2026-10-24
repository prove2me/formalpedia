-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P30.renyi_noncontinuity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T17:13:36.258978+00:00
-- url     : https://prove2.me/submissions/2ffa39be-85b4-4db8-8247-9121a28c3040

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P30

-- ===== RN1 =====

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder
open Filter

set_option linter.unusedSectionVars false

namespace X4RN

open QAlgorithms QAlgorithms.Papers.Independent.Frontier30.P30

section diag
variable {X : Type*} [Fintype X] [DecidableEq X]

open Polynomial in
lemma cfc_diag (d : X → ℝ) (f : ℝ → ℝ) :
    cfc f (Matrix.diagonal (fun i => (d i : ℂ))) = Matrix.diagonal (fun i => (f (d i) : ℂ)) := by
  set A := Matrix.diagonal (fun i => (d i : ℂ)) with hA
  have hsa : IsSelfAdjoint A := by
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, hA, Matrix.diagonal_conjTranspose]
    congr 1; funext i; simp
  set S : Finset ℝ := Finset.univ.image d
  let p : ℝ[X] := Lagrange.interpolate S id f
  have hp : ∀ i, p.eval (d i) = f (d i) := by
    intro i
    exact Lagrange.eval_interpolate_at_node (s := S) (v := id) (r := f) (i := d i)
      (Set.injOn_id _) (Finset.mem_image_of_mem d (Finset.mem_univ i))
  have hspec : ∀ x ∈ spectrum ℝ A, ∃ i, d i = x := by
    intro x hx
    rw [← spectrum.preimage_algebraMap ℂ, Set.mem_preimage, hA, spectrum_diagonal,
      Set.mem_range] at hx
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, by rw [Complex.coe_algebraMap] at hi; exact_mod_cast hi⟩
  have h1 : cfc f A = cfc p.eval A := by
    apply cfc_congr
    intro x hx
    obtain ⟨i, rfl⟩ := hspec x hx
    exact (hp i).symm
  rw [h1, cfc_polynomial p A]
  rw [hA, show Matrix.diagonal (fun i => (d i : ℂ)) =
    Matrix.diagonalAlgHom ℝ (fun i => (d i : ℂ)) from rfl, Polynomial.aeval_algHom_apply]
  rw [show Matrix.diagonal (fun i => (f (d i) : ℂ)) =
    Matrix.diagonalAlgHom ℝ (fun i => (f (d i) : ℂ)) from rfl]
  congr 1
  funext i
  rw [Polynomial.aeval_pi_apply₂]
  rw [show ((d i : ℝ) : ℂ) = algebraMap ℝ ℂ (d i) from rfl, Polynomial.aeval_algebraMap_apply,
    Polynomial.aeval_def, Algebra.algebraMap_self, ← Polynomial.eval, hp]
  rfl

lemma tr_cfc_diag (d : X → ℝ) (f : ℝ → ℝ) :
    (cfc f (Matrix.diagonal (fun i => (d i : ℂ)))).trace.re = ∑ i, f (d i) := by
  rw [cfc_diag, Matrix.trace_diagonal, Complex.re_sum]
  simp

lemma traceNorm_diag (e : X → ℝ) :
    traceNorm (Matrix.diagonal fun i => (e i : ℂ)) = ∑ i, |e i| := by
  unfold traceNorm
  have h : (Matrix.diagonal fun i => (e i : ℂ))ᴴ * Matrix.diagonal (fun i => (e i : ℂ)) =
      Matrix.diagonal fun i => ((e i ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    congr 1; funext i
    simp [sq]
  rw [h, tr_cfc_diag]
  simp [Real.sqrt_sq_eq_abs]

lemma diag_density (d : X → ℝ) (h0 : ∀ i, 0 ≤ d i) (h1 : ∑ i, d i = 1) :
    IsDensityMatrix (Matrix.diagonal fun i => (d i : ℂ)) := by
  refine ⟨Matrix.PosSemidef.diagonal fun i => ?_, ?_⟩
  · simp only [Pi.zero_apply]; exact_mod_cast h0 i
  · rw [Matrix.trace_diagonal]; exact_mod_cast h1

end diag

section prod

lemma prod_exp {n : ℕ} {M : Type*} [Fintype M] (f : Fin n → M → ℝ) :
    ∑ x : Fin n → M, ∏ i, f i (x i) = ∏ i, ∑ a, f i a := by
  rw [Finset.prod_univ_sum (fun _ => Finset.univ) f, Fintype.piFinset_univ]

lemma pq_pos (a : Fin 2) : 0 < qubitProbability a := by
  fin_cases a <;> simp [qubitProbability]

lemma pq_sum : ∑ a, qubitProbability a = 1 := by
  simp [Fin.sum_univ_two, qubitProbability]; norm_num

/-- product weight. -/
def w (n : ℕ) (x : Fin n → Fin 2) : ℝ := ∏ i, qubitProbability (x i)

lemma w_pos (n : ℕ) (x : Fin n → Fin 2) : 0 < w n x :=
  Finset.prod_pos fun i _ => pq_pos _

lemma w_sum (n : ℕ) : ∑ x, w n x = 1 := by
  unfold w
  rw [prod_exp (fun _ a => qubitProbability a)]
  simp only [pq_sum, Finset.prod_const_one]

lemma var_sum (n : ℕ) (g : Fin 2 → ℝ) (hg : ∑ a, qubitProbability a * g a = 0) :
    ∑ x : Fin n → Fin 2, w n x * (∑ i, g (x i)) ^ 2 =
      n * ∑ a, qubitProbability a * g a ^ 2 := by
  have e : ∀ x : Fin n → Fin 2, w n x * (∑ i, g (x i)) ^ 2 =
      ∑ i, ∑ j, ∏ k, (qubitProbability (x k) *
        ((if k = i then g (x k) else 1) * (if k = j then g (x k) else 1))) := by
    intro x
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_ite_eq',
      Finset.prod_ite_eq']
    simp [w]
  rw [Finset.sum_congr rfl fun x _ => e x, Finset.sum_comm]
  have e2 : ∀ i : Fin n, ∑ x : Fin n → Fin 2, ∑ j, ∏ k, (qubitProbability (x k) *
        ((if k = i then g (x k) else 1) * (if k = j then g (x k) else 1))) =
      ∑ a, qubitProbability a * g a ^ 2 := by
    intro i
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single i]
    · rw [prod_exp (fun k a => qubitProbability a *
        ((if k = i then g a else 1) * (if k = i then g a else 1)))]
      rw [Finset.prod_eq_single i]
      · simp [sq]
      · intro k _ hk
        simp only [if_neg hk, mul_one, pq_sum]
      · simp
    · intro j _ hj
      rw [prod_exp (fun k a => qubitProbability a *
        ((if k = i then g a else 1) * (if k = j then g a else 1)))]
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      rw [← hg]
      exact Finset.sum_congr rfl fun a _ => by rw [if_neg hj, if_pos rfl, one_mul]
    · simp
  rw [Finset.sum_congr rfl fun i _ => e2 i]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end prod

end X4RN

-- ===== RN2 =====

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder
open Filter

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X4RN

open QAlgorithms QAlgorithms.Papers.Independent.Frontier30.P30
open QAlgorithms.Papers.Independent.Information100.P80 (log2)

lemma log2_eq (x : ℝ) : log2 x = Real.logb 2 x := rfl

/-- surprisal of one letter. -/
def sp (a : Fin 2) : ℝ := -Real.logb 2 (qubitProbability a)

lemma H_eq : witnessEntropy = ∑ a, qubitProbability a * sp a := by
  unfold witnessEntropy sp
  simp only [log2_eq, mul_neg, Finset.sum_neg_distrib]

lemma lw (n : ℕ) (x : Fin n → Fin 2) : -Real.logb 2 (w n x) = ∑ i, sp (x i) := by
  unfold w sp
  rw [Real.logb, Real.log_prod (fun i _ => (pq_pos (x i)).ne'), Finset.sum_div,
    ← Finset.sum_neg_distrib]
  rfl

/-- the window. -/
def dl (n : ℕ) : ℝ := (n : ℝ) ^ (-(1 / 4 : ℝ))

/-- kept predicate. -/
abbrev Kp (n : ℕ) (x : Fin n → Fin 2) : Prop :=
  n = 0 ∨ |(-log2 (w n x)) / (n : ℝ) - witnessEntropy| ≤ dl n

lemma kept_eq (n : ℕ) (x : Fin n → Fin 2) :
    keptWeight n x = if Kp n x then w n x else 0 := rfl

/-- retained mass. -/
def ms (n : ℕ) : ℝ := ∑ x, keptWeight n x

lemma kept_nonneg (n : ℕ) (x : Fin n → Fin 2) : 0 ≤ keptWeight n x := by
  rw [kept_eq]; split_ifs
  · exact (w_pos n x).le
  · exact le_rfl

lemma kept_le (n : ℕ) (x : Fin n → Fin 2) : keptWeight n x ≤ w n x := by
  rw [kept_eq]; split_ifs
  · exact le_rfl
  · exact (w_pos n x).le

lemma ms_le (n : ℕ) : ms n ≤ 1 := by
  rw [← w_sum n]; exact Finset.sum_le_sum fun x _ => kept_le n x

lemma ms_nonneg (n : ℕ) : 0 ≤ ms n := Finset.sum_nonneg fun x _ => kept_nonneg n x

/-- per-letter variance. -/
def vv : ℝ := ∑ a, qubitProbability a * (sp a - witnessEntropy) ^ 2

lemma dl_sq (n : ℕ) (hn : 1 ≤ n) : (n : ℝ) * dl n ^ 2 = (n : ℝ) ^ (1 / 2 : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold dl
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn'.le]
  conv_lhs => arg 1; rw [← Real.rpow_one (n : ℝ)]
  rw [← Real.rpow_add hn']
  norm_num

lemma cheb (n : ℕ) (hn : 1 ≤ n) : 1 - ms n ≤ vv * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : 0 < dl n := Real.rpow_pos_of_pos hn' _
  set g : Fin 2 → ℝ := fun a => sp a - witnessEntropy with hg
  have hg0 : ∑ a, qubitProbability a * g a = 0 := by
    simp only [hg, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, pq_sum, one_mul, ← H_eq]
    ring
  have hv := var_sum n g hg0
  have hD : 0 < ((n : ℝ) * dl n) ^ 2 := by positivity
  have hx : ∀ x, w n x - keptWeight n x ≤ w n x * (∑ i, g (x i)) ^ 2 / ((n : ℝ) * dl n) ^ 2 := by
    intro x
    rw [kept_eq]
    split_ifs with hk
    · rw [sub_self]; exact div_nonneg (mul_nonneg (w_pos n x).le (sq_nonneg _)) hD.le
    · rw [sub_zero, le_div_iff₀ hD]
      have hk' : dl n < |(-log2 (w n x)) / (n : ℝ) - witnessEntropy| := by
        unfold Kp at hk; push Not at hk; exact hk.2
      have e : (-log2 (w n x)) / (n : ℝ) - witnessEntropy = (∑ i, g (x i)) / n := by
        rw [log2_eq, lw]
        simp only [hg, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        field_simp
      rw [e, abs_div, abs_of_pos hn', lt_div_iff₀ hn'] at hk'
      have : ((n : ℝ) * dl n) ^ 2 ≤ (∑ i, g (x i)) ^ 2 := by
        rw [← sq_abs (∑ i, g (x i))]
        have : 0 ≤ (n : ℝ) * dl n := by positivity
        nlinarith
      nlinarith [(w_pos n x).le]
  have hs := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => hx x
  rw [Finset.sum_sub_distrib, w_sum] at hs
  rw [← Finset.sum_div, hv] at hs
  unfold ms
  refine hs.trans (le_of_eq ?_)
  rw [mul_pow, show (n : ℝ) ^ 2 * dl n ^ 2 = n * (n * dl n ^ 2) by ring, dl_sq n hn]
  have e2 : (n : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / (n : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Real.rpow_neg hn'.le, inv_eq_one_div]
  rw [e2]
  have : (0 : ℝ) < (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hn' _
  field_simp
  simp [vv, hg]

lemma ms_tendsto : Tendsto ms atTop (nhds 1) := by
  have h1 : Tendsto (fun n : ℕ => 1 - vv * (n : ℝ) ^ (-(1 / 2 : ℝ))) atTop (nhds 1) := by
    have : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 2 : ℝ))) atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
    simpa using (this.const_mul vv).const_sub 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    linarith [cheb n hn]
  · exact Eventually.of_forall ms_le

end X4RN

-- ===== RN3 =====

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder
open Filter

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X4RN

open QAlgorithms QAlgorithms.Papers.Independent.Frontier30.P30
open QAlgorithms.Papers.Independent.Information100.P80 (log2)
open QAlgorithms.Papers.Independent.Dependency50.P05 (renyiEntropy)

lemma qubit_eq (n : ℕ) : qubitCopies n = Matrix.diagonal fun x => ((w n x : ℝ) : ℂ) := rfl

lemma typ_eq (n : ℕ) (h : ms n ≠ 0) :
    typicalCopies n = Matrix.diagonal fun x => ((keptWeight n x / ms n : ℝ) : ℂ) := by
  unfold typicalCopies
  simp only
  rw [if_neg (show ¬ (∑ x, keptWeight n x) = 0 from h)]
  rfl

lemma typ_zero (n : ℕ) (h : ms n = 0) : typicalCopies n = qubitCopies n := by
  unfold typicalCopies
  simp only
  rw [if_pos (show (∑ x, keptWeight n x) = 0 from h)]

lemma qubit_density (n : ℕ) : IsDensityMatrix (qubitCopies n) := by
  rw [qubit_eq]
  exact diag_density _ (fun x => (w_pos n x).le) (w_sum n)

lemma typ_density (n : ℕ) : IsDensityMatrix (typicalCopies n) := by
  by_cases h : ms n = 0
  · rw [typ_zero n h]; exact qubit_density n
  · have hm : 0 < ms n := lt_of_le_of_ne (ms_nonneg n) (Ne.symm h)
    rw [typ_eq n h]
    refine diag_density _ (fun x => div_nonneg (kept_nonneg n x) hm.le) ?_
    rw [← Finset.sum_div]
    exact div_self h

lemma tn_typ (n : ℕ) (hm : 0 < ms n) :
    traceNorm (typicalCopies n - qubitCopies n) = 2 * (1 - ms n) := by
  rw [typ_eq n hm.ne', qubit_eq, Matrix.diagonal_sub]
  have e : (fun x => ((keptWeight n x / ms n : ℝ) : ℂ) - ((w n x : ℝ) : ℂ)) =
      fun x => ((keptWeight n x / ms n - w n x : ℝ) : ℂ) := by
    funext x; push_cast; ring
  rw [e, traceNorm_diag]
  have hx : ∀ x, |keptWeight n x / ms n - w n x| =
      keptWeight n x / ms n - keptWeight n x + (w n x - keptWeight n x) := by
    intro x
    have hw := w_pos n x
    rw [kept_eq]
    split_ifs
    · rw [sub_self, add_zero, abs_of_nonneg]
      rw [sub_nonneg, le_div_iff₀ hm]
      nlinarith [ms_le n]
    · simp only [zero_div, zero_sub, abs_neg, abs_of_pos hw, sub_zero, zero_add]
  rw [Finset.sum_congr rfl fun x _ => hx x, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, ← Finset.sum_div, w_sum]
  change ms n / ms n - ms n + (1 - ms n) = _
  rw [div_self hm.ne']
  ring

/-- weights entering the Rényi trace. -/
def G (β : ℝ) (n : ℕ) (x : Fin n → Fin 2) : ℝ := if Kp n x then w n x ^ β else 0

lemma w_rpow (β : ℝ) (n : ℕ) (x : Fin n → Fin 2) :
    w n x ^ β = w n x * (2 : ℝ) ^ ((1 - β) * (-Real.logb 2 (w n x))) := by
  have hw := w_pos n x
  have : (2 : ℝ) ^ ((1 - β) * (-Real.logb 2 (w n x))) = w n x ^ (β - 1) := by
    rw [show (1 - β) * (-Real.logb 2 (w n x)) = Real.logb 2 (w n x) * (β - 1) by ring,
      Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hw]
  rw [this]
  conv_lhs => rw [show β = 1 + (β - 1) by ring]
  rw [Real.rpow_add hw, Real.rpow_one]

end X4RN

-- ===== RN4 =====

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder
open Filter

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X4RN

open QAlgorithms QAlgorithms.Papers.Independent.Frontier30.P30
open QAlgorithms.Papers.Independent.Information100.P80 (log2)
open QAlgorithms.Papers.Independent.Dependency50.P05 (renyiEntropy)

lemma G_bounds (β : ℝ) (h1 : β < 1) (n : ℕ) (hn : 1 ≤ n) (x : Fin n → Fin 2) :
    keptWeight n x * (2 : ℝ) ^ ((1 - β) * (n * (witnessEntropy - dl n))) ≤ G β n x ∧
      G β n x ≤ keptWeight n x * (2 : ℝ) ^ ((1 - β) * (n * (witnessEntropy + dl n))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold G
  rw [kept_eq]
  split_ifs with hk
  · have hk' : |(-log2 (w n x)) / (n : ℝ) - witnessEntropy| ≤ dl n := by
      rcases hk with h | h
      · omega
      · exact h
    rw [log2_eq, abs_le] at hk'
    obtain ⟨ha, hb⟩ := hk'
    have l1 : (n : ℝ) * (witnessEntropy - dl n) ≤ -Real.logb 2 (w n x) := by
      have := (le_div_iff₀ hn').1 (by linarith : witnessEntropy - dl n ≤ -Real.logb 2 (w n x) / n)
      linarith
    have l2 : -Real.logb 2 (w n x) ≤ (n : ℝ) * (witnessEntropy + dl n) := by
      have := (div_le_iff₀ hn').1 (by linarith : -Real.logb 2 (w n x) / n ≤ witnessEntropy + dl n)
      linarith
    have hb1 : (0 : ℝ) ≤ 1 - β := by linarith
    have hw := (w_pos n x).le
    rw [w_rpow]
    constructor
    · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_left l1 hb1)) hw
    · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_left l2 hb1)) hw
  · simp

lemma typ_R (β : ℝ) (h0 : 0 ≤ β) (h1 : β < 1) (n : ℕ) (hm : 0 < ms n)
    (hG : 0 < ∑ x, G β n x) :
    (1 - β) * renyiEntropy β (typicalCopies n) =
      Real.logb 2 (∑ x, G β n x) - β * Real.logb 2 (ms n) := by
  rw [typ_eq n hm.ne']
  unfold renyiEntropy
  by_cases hβ : β = 0
  · rw [if_pos hβ, tr_cfc_diag]
    subst hβ
    have e : ∀ x, (if keptWeight n x / ms n = 0 then (0 : ℝ) else 1) = G 0 n x := by
      intro x
      unfold G
      rw [kept_eq]
      by_cases hk : Kp n x
      · simp only [if_pos hk, Real.rpow_zero, div_eq_zero_iff, (w_pos n x).ne', hm.ne', or_self,
          if_false]
      · simp only [if_neg hk, zero_div, if_true]
    simp only [e]
    ring
  · have hβ1 : β ≠ 1 := by intro h; linarith
    rw [if_neg hβ, if_neg hβ1, tr_cfc_diag]
    have e : ∀ x, (keptWeight n x / ms n) ^ β = G β n x / ms n ^ β := by
      intro x
      unfold G
      rw [kept_eq]
      split_ifs
      · exact Real.div_rpow (w_pos n x).le hm.le β
      · rw [zero_div, Real.zero_rpow hβ, zero_div]
    simp only [e]
    rw [← Finset.sum_div, Real.logb_div hG.ne' (Real.rpow_pos_of_pos hm β).ne',
      Real.logb_rpow_eq_mul_logb_of_pos hm]
    have : (1 : ℝ) - β ≠ 0 := by intro h; apply hβ1; linarith
    field_simp

lemma typ_bounds (β : ℝ) (h0 : 0 ≤ β) (h1 : β < 1) (n : ℕ) (hn : 1 ≤ n) (hm : 0 < ms n) :
    Real.logb 2 (ms n) + n * (witnessEntropy - dl n) ≤ renyiEntropy β (typicalCopies n) ∧
      renyiEntropy β (typicalCopies n) ≤ Real.logb 2 (ms n) + n * (witnessEntropy + dl n) := by
  set A := (2 : ℝ) ^ ((1 - β) * (n * (witnessEntropy - dl n)))
  set B := (2 : ℝ) ^ ((1 - β) * (n * (witnessEntropy + dl n)))
  have hA : 0 < A := Real.rpow_pos_of_pos (by norm_num) _
  have hB : 0 < B := Real.rpow_pos_of_pos (by norm_num) _
  have s1 : ms n * A ≤ ∑ x, G β n x := by
    unfold ms
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun x _ => (G_bounds β h1 n hn x).1
  have s2 : ∑ x, G β n x ≤ ms n * B := by
    unfold ms
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun x _ => (G_bounds β h1 n hn x).2
  have hG : 0 < ∑ x, G β n x := lt_of_lt_of_le (mul_pos hm hA) s1
  have hR := typ_R β h0 h1 n hm hG
  have l1 : Real.logb 2 (ms n) + (1 - β) * (n * (witnessEntropy - dl n)) ≤
      Real.logb 2 (∑ x, G β n x) := by
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (mul_pos hm hA) s1
    rwa [Real.logb_mul hm.ne' hA.ne', Real.logb_rpow (by norm_num) (by norm_num)] at this
  have l2 : Real.logb 2 (∑ x, G β n x) ≤
      Real.logb 2 (ms n) + (1 - β) * (n * (witnessEntropy + dl n)) := by
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) hG s2
    rwa [Real.logb_mul hm.ne' hB.ne', Real.logb_rpow (by norm_num) (by norm_num)] at this
  have hb : 0 < 1 - β := by linarith
  constructor
  · refine le_of_mul_le_mul_left ?_ hb
    rw [hR]; nlinarith
  · refine le_of_mul_le_mul_left ?_ hb
    rw [hR]; nlinarith

end X4RN

-- ===== RN5 =====

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder
open Filter

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X4RN

open QAlgorithms QAlgorithms.Papers.Independent.Frontier30.P30
open QAlgorithms.Papers.Independent.Information100.P80 (log2)
open QAlgorithms.Papers.Independent.Dependency50.P05 (renyiEntropy)

/-- one-copy Rényi entropy. -/
def Rq (β : ℝ) : ℝ :=
  if β = 0 then 1 else Real.logb 2 (∑ a, qubitProbability a ^ β) / (1 - β)

lemma qubit_R (β : ℝ) (h1 : β < 1) (n : ℕ) :
    renyiEntropy β (qubitCopies n) = n * Rq β := by
  rw [qubit_eq]
  unfold renyiEntropy Rq
  by_cases hβ : β = 0
  · rw [if_pos hβ, if_pos hβ, tr_cfc_diag]
    simp only [(w_pos n _).ne', if_false, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  · have hβ1 : β ≠ 1 := by intro h; linarith
    rw [if_neg hβ, if_neg hβ1, if_neg hβ, tr_cfc_diag]
    have e : ∀ x : Fin n → Fin 2, w n x ^ β = ∏ i, qubitProbability (x i) ^ β := by
      intro x
      unfold w
      rw [Real.finset_prod_rpow _ _ (fun i _ => (pq_pos _).le)]
    simp only [e]
    rw [prod_exp (fun _ a => qubitProbability a ^ β), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Real.logb_pow, mul_div_assoc]

lemma H_log : witnessEntropy * Real.log 2 =
    -((1 / 4 : ℝ) * Real.log (1 / 4) + (3 / 4) * Real.log (3 / 4)) := by
  rw [H_eq]
  simp only [Fin.sum_univ_two, sp, qubitProbability, Real.logb]
  norm_num
  field_simp
  ring

lemma Rq_gt (β : ℝ) (h0 : 0 ≤ β) (h1 : β < 1) : witnessEntropy < Rq β := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hH := H_log
  have l4 : Real.log (1 / 4) = -(2 * Real.log 2) := by
    rw [one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have l34 : Real.log (3 / 4) = Real.log 3 - 2 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  unfold Rq
  by_cases hβ : β = 0
  · rw [if_pos hβ]
    have h16 : Real.log 16 < Real.log 27 := Real.log_lt_log (by norm_num) (by norm_num)
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow,
      Real.log_pow] at h16
    push_cast at h16
    rw [l4, l34] at hH
    by_contra hc
    push Not at hc
    nlinarith
  · rw [if_neg hβ]
    have hb : 0 < 1 - β := by linarith
    set x := (1 / 4 : ℝ) ^ (β - 1)
    set y := (3 / 4 : ℝ) ^ (β - 1)
    have hx : 0 < x := Real.rpow_pos_of_pos (by norm_num) _
    have hy : 0 < y := Real.rpow_pos_of_pos (by norm_num) _
    have hxy : y < x := Real.rpow_lt_rpow_of_neg (by norm_num) (by norm_num) (by linarith)
    have hc := strictConcaveOn_log_Ioi.2 (Set.mem_Ioi.2 hx) (Set.mem_Ioi.2 hy) hxy.ne'
      (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num)
    simp only [smul_eq_mul] at hc
    have ex : (1 / 4 : ℝ) * x = (1 / 4 : ℝ) ^ β := by
      conv_rhs => rw [show β = 1 + (β - 1) by ring]
      rw [Real.rpow_add (by norm_num), Real.rpow_one]
    have ey : (3 / 4 : ℝ) * y = (3 / 4 : ℝ) ^ β := by
      conv_rhs => rw [show β = 1 + (β - 1) by ring]
      rw [Real.rpow_add (by norm_num), Real.rpow_one]
    rw [ex, ey, Real.log_rpow (by norm_num), Real.log_rpow (by norm_num)] at hc
    have hS : ∑ a, qubitProbability a ^ β = (1 / 4 : ℝ) ^ β + (3 / 4 : ℝ) ^ β := by
      simp [Fin.sum_univ_two, qubitProbability]
    rw [hS, Real.logb, lt_div_iff₀ hb, lt_div_iff₀ hl2]
    nlinarith

end X4RN

-- ===== RN6 =====

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder
open Filter

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X4RN

open QAlgorithms QAlgorithms.Papers.Independent.Frontier30.P30
open QAlgorithms.Papers.Independent.Information100.P80 (log2)
open QAlgorithms.Papers.Independent.Dependency50.P05 (renyiEntropy)

lemma dl_tendsto : Tendsto dl atTop (nhds 0) :=
  (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop

lemma logm_tendsto : Tendsto (fun n => Real.logb 2 (ms n) / (n : ℝ)) atTop (nhds 0) := by
  have h : Tendsto (fun n => Real.logb 2 (ms n)) atTop (nhds (Real.logb 2 1)) :=
    ((Real.continuousAt_log one_ne_zero).tendsto.comp ms_tendsto).div_const _
  rw [Real.logb_one] at h
  exact h.div_atTop tendsto_natCast_atTop_atTop

lemma ms_pos_ev : ∀ᶠ n in atTop, 0 < ms n :=
  ms_tendsto.eventually (lt_mem_nhds (by norm_num))

lemma typ_tendsto (β : ℝ) (h0 : 0 ≤ β) (h1 : β < 1) :
    Tendsto (fun n => renyiEntropy β (typicalCopies n) / (n : ℝ)) atTop
      (nhds witnessEntropy) := by
  have lo : Tendsto (fun n => Real.logb 2 (ms n) / (n : ℝ) + (witnessEntropy - dl n)) atTop
      (nhds witnessEntropy) := by
    simpa using logm_tendsto.add (tendsto_const_nhds.sub dl_tendsto)
  have up : Tendsto (fun n => Real.logb 2 (ms n) / (n : ℝ) + (witnessEntropy + dl n)) atTop
      (nhds witnessEntropy) := by
    simpa using logm_tendsto.add (tendsto_const_nhds.add dl_tendsto)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' lo up ?_ ?_
  · filter_upwards [ms_pos_ev, eventually_ge_atTop 1] with n hm hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have := (typ_bounds β h0 h1 n hn hm).1
    rw [le_div_iff₀ hn']
    have e : (Real.logb 2 (ms n) / (n : ℝ) + (witnessEntropy - dl n)) * n =
        Real.logb 2 (ms n) + n * (witnessEntropy - dl n) := by field_simp
    rw [e]; exact this
  · filter_upwards [ms_pos_ev, eventually_ge_atTop 1] with n hm hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have := (typ_bounds β h0 h1 n hn hm).2
    rw [div_le_iff₀ hn']
    have e : (Real.logb 2 (ms n) / (n : ℝ) + (witnessEntropy + dl n)) * n =
        Real.logb 2 (ms n) + n * (witnessEntropy + dl n) := by field_simp
    rw [e]; exact this

lemma qubit_tendsto (β : ℝ) (h1 : β < 1) :
    Tendsto (fun n => renyiEntropy β (qubitCopies n) / (n : ℝ)) atTop
      (nhds (renyiEntropy β (qubitCopies 1))) := by
  rw [qubit_R β h1 1, Nat.cast_one, one_mul]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [qubit_R β h1 n]
  field_simp

theorem main (alpha : ℝ) (ha : 0 ≤ alpha) (hb : alpha < 1) :
    (∀ n, IsDensityMatrix (qubitCopies n) ∧ IsDensityMatrix (typicalCopies n)) ∧
    Tendsto (fun n => traceNorm (typicalCopies n - qubitCopies n)) atTop (nhds 0) ∧
    Tendsto (fun n => renyiEntropy alpha (typicalCopies n) / (n : ℝ))
      atTop (nhds witnessEntropy) ∧
    Tendsto (fun n => renyiEntropy alpha (qubitCopies n) / (n : ℝ))
      atTop (nhds (renyiEntropy alpha (qubitCopies 1))) ∧
    0 < renyiEntropy alpha (qubitCopies 1) - witnessEntropy ∧
    Tendsto (fun n => |renyiEntropy alpha (qubitCopies n) -
      renyiEntropy alpha (typicalCopies n)| / (n : ℝ)) atTop
      (nhds (renyiEntropy alpha (qubitCopies 1) - witnessEntropy)) := by
  have hpos : 0 < renyiEntropy alpha (qubitCopies 1) - witnessEntropy := by
    rw [qubit_R alpha hb 1, Nat.cast_one, one_mul]
    linarith [Rq_gt alpha ha hb]
  refine ⟨fun n => ⟨qubit_density n, typ_density n⟩, ?_, typ_tendsto alpha ha hb,
    qubit_tendsto alpha hb, hpos, ?_⟩
  · have h : Tendsto (fun n => 2 * (1 - ms n)) atTop (nhds 0) := by
      simpa using (ms_tendsto.const_sub 1).const_mul 2
    refine h.congr' ?_
    filter_upwards [ms_pos_ev] with n hm
    exact (tn_typ n hm).symm
  · have h := ((qubit_tendsto alpha hb).sub (typ_tendsto alpha ha hb)).abs
    rw [abs_of_pos hpos] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [← sub_div, abs_div, abs_of_pos hn']

end X4RN

-- ===== RNSol =====

noncomputable section

open scoped Matrix ComplexConjugate
open Filter

attribute [local instance] Classical.propDecidable Classical.decEq

section
open QAlgorithms QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Frontier30.P30
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open QAlgorithms.Papers.Independent.Information100.P80 (log2)

theorem solution (alpha : ℝ) (ha : 0 ≤ alpha) (hb : alpha < 1) :
    (∀ n, IsDensityMatrix (qubitCopies n) ∧ IsDensityMatrix (typicalCopies n)) ∧
    Tendsto (fun n => traceNorm (typicalCopies n-qubitCopies n)) atTop (nhds 0) ∧
    Tendsto (fun n => Dependency50.P05.renyiEntropy alpha (typicalCopies n)/(n : ℝ))
      atTop (nhds witnessEntropy) ∧
    Tendsto (fun n => Dependency50.P05.renyiEntropy alpha (qubitCopies n)/(n : ℝ))
      atTop (nhds (Dependency50.P05.renyiEntropy alpha (qubitCopies 1))) ∧
    0 < Dependency50.P05.renyiEntropy alpha (qubitCopies 1)-witnessEntropy ∧
    Tendsto (fun n => |Dependency50.P05.renyiEntropy alpha (qubitCopies n)-
      Dependency50.P05.renyiEntropy alpha (typicalCopies n)|/(n : ℝ)) atTop
      (nhds (Dependency50.P05.renyiEntropy alpha (qubitCopies 1)-witnessEntropy)) :=
  X4RN.main alpha ha hb

end

end
