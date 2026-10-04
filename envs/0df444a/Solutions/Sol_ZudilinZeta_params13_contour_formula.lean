-- Prove2me | solution 1 for ZudilinZeta.params13_contour_formula
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-02T11:46:46.494999+00:00
-- url     : https://prove2.me/submissions/f084aebb-6b89-43ee-9f08-8ca2bf1bc6a1

import Definitions.Def_ZudilinZetaContourKernel
import Definitions.Def_ZudilinZetaParams13
import Definitions.Def_ZudilinZetaPartialFractions
import Definitions.Def_ZudilinZetaSetup
import Mathlib
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic
import Theorems.Thm_Zeta23_Analytic_rectangleIntegralPrime_mul_logDeriv_of_poles
import Theorems.Thm_ZudilinZeta_zudilin_series_summable

set_option autoImplicit false


-- Source module: missions.zudilin.Params13KernelHolomorphic
section
set_option autoImplicit false
noncomputable section
open Complex Finset Set Filter Topology

namespace ZudilinZeta

lemma contour_gamma_base_re_ge_one {z : ℂ} (hz : 87 ≤ z.re ∧ z.re ≤ 175 / 2)
    (i : ℕ) (hi : i ∈ Finset.range 39) : 1 ≤ (params13GammaBase z i).re := by
  have hi' : i < 39 := Finset.mem_range.mp hi
  interval_cases i <;>
    norm_num [params13GammaWeight, params13GammaBase, params13GammaSlope,
      params13GammaOffset, eta13, Complex.mul_re] <;> linarith

lemma params13_gamma_argument_re_pos (n : ℕ) (hn : 2 ≤ n) {z : ℂ}
    (hz : 87 ≤ z.re ∧ z.re ≤ 175 / 2) (i : ℕ) (hi : i ∈ Finset.range 39) :
    0 < ((n : ℂ) * params13GammaBase z i + (params13GammaShiftIndex i : ℂ)).re := by
  have hbase := contour_gamma_base_re_ge_one hz i hi
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hshift : (-1 : ℝ) ≤ (params13GammaShiftIndex i : ℝ) := by
    unfold params13GammaShiftIndex
    split_ifs <;> norm_num
  simp only [add_re, mul_re, natCast_re, natCast_im, zero_mul, sub_zero, intCast_re]
  nlinarith

lemma differentiableAt_params13GammaKernel (n : ℕ) (hn : 2 ≤ n) {z : ℂ}
    (hz : 87 ≤ z.re ∧ z.re ≤ 175 / 2) :
    DifferentiableAt ℂ (params13GammaKernel n) z := by
  have hΓ (i : ℕ) (hi : i ∈ range 39) :
      DifferentiableAt ℂ (fun z : ℂ =>
        Complex.Gamma ((n : ℂ) * params13GammaBase z i + (params13GammaShiftIndex i : ℂ)) ^
          params13GammaWeight i) z := by
    have hpos := params13_gamma_argument_re_pos n hn hz i hi
    have hnot (m : ℕ) : (n : ℂ) * params13GammaBase z i +
        (params13GammaShiftIndex i : ℂ) ≠ -(m : ℂ) := by
      intro he
      have h := congrArg Complex.re he
      simp only [neg_re, natCast_re] at h
      linarith [Nat.cast_nonneg (α := ℝ) m]
    have harg : DifferentiableAt ℂ (fun w : ℂ =>
        (n : ℂ) * params13GammaBase w i + (params13GammaShiftIndex i : ℂ)) z := by
      unfold params13GammaBase
      fun_prop
    exact ((Complex.differentiableAt_Gamma _ hnot).comp z harg).zpow
      (Or.inl (Complex.Gamma_ne_zero hnot))
  unfold params13GammaKernel
  exact (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => 91 * (n : ℂ) + 2 - 2 * (n : ℂ) * z) z).mul
    (DifferentiableAt.fun_finset_prod (fun i hi => hΓ i hi))

end ZudilinZeta
end
end


-- Source module: missions.zudilin.DecayFromConvergence
section
/-
The rational-function degree bookkeeping below is reused from mrfancypants,
accepted Prove2Me submission 85b357a0-c802-42df-a9b9-9d6ed8493709,
for the mission series-convergence theorem. The final decay consequence is new.
-/

set_option autoImplicit false

namespace ZudilinZeta

open Polynomial Filter Asymptotics Topology

/-- `f` agrees on `(-1, ∞)` with a ratio `A / B` of real polynomials, `B` nonvanishing there,
and `deg A - deg B ≤ d`. -/
def aux_zz_RD (f : ℝ → ℝ) (d : ℤ) : Prop :=
  ∃ A B : ℝ[X], (∀ t : ℝ, -1 < t → B.eval t ≠ 0) ∧
    (∀ t : ℝ, -1 < t → f t = A.eval t / B.eval t) ∧ (A.natDegree : ℤ) - B.natDegree ≤ d

theorem aux_zz_RD_mono {f : ℝ → ℝ} {d d' : ℤ} (h : aux_zz_RD f d) (hd : d ≤ d') :
    aux_zz_RD f d' := by
  obtain ⟨A, B, h1, h2, h3⟩ := h
  exact ⟨A, B, h1, h2, h3.trans hd⟩

theorem aux_zz_RD_congr {f g : ℝ → ℝ} {d : ℤ} (h : aux_zz_RD f d)
    (hfg : ∀ t : ℝ, -1 < t → f t = g t) : aux_zz_RD g d := by
  obtain ⟨A, B, h1, h2, h3⟩ := h
  exact ⟨A, B, h1, fun t ht => (hfg t ht).symm.trans (h2 t ht), h3⟩

theorem aux_zz_RD_mul {f g : ℝ → ℝ} {d₁ d₂ : ℤ} (hf : aux_zz_RD f d₁) (hg : aux_zz_RD g d₂) :
    aux_zz_RD (fun t => f t * g t) (d₁ + d₂) := by
  obtain ⟨A₁, B₁, h1, h2, h3⟩ := hf
  obtain ⟨A₂, B₂, h1', h2', h3'⟩ := hg
  have hB₁ : B₁ ≠ 0 := by
    intro h; exact h1 0 (by norm_num) (by simp [h])
  have hB₂ : B₂ ≠ 0 := by
    intro h; exact h1' 0 (by norm_num) (by simp [h])
  refine ⟨A₁ * A₂, B₁ * B₂, ?_, ?_, ?_⟩
  · intro t ht
    rw [eval_mul]
    exact mul_ne_zero (h1 t ht) (h1' t ht)
  · intro t ht
    show f t * g t = _
    rw [eval_mul, eval_mul, h2 t ht, h2' t ht, div_mul_div_comm]
  · rw [natDegree_mul hB₁ hB₂]
    have : ((A₁ * A₂).natDegree : ℤ) ≤ A₁.natDegree + A₂.natDegree := by
      exact_mod_cast natDegree_mul_le
    push_cast
    linarith

theorem aux_zz_RD_const (c : ℝ) : aux_zz_RD (fun _ => c) 0 := by
  refine ⟨C c, 1, fun t _ => by simp, fun t _ => by simp, by simp⟩

theorem aux_zz_RD_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (d : ι → ℤ)
    (h : ∀ i ∈ s, aux_zz_RD (f i) (d i)) :
    aux_zz_RD (fun t => ∏ i ∈ s, f i t) (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact aux_zz_RD_const 1
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine aux_zz_RD_congr (aux_zz_RD_mul (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))) ?_
    intro t _
    rw [Finset.prod_insert ha]

theorem aux_zz_RD_lin (c : ℝ) : aux_zz_RD (fun t => c + 2 * t) 1 := by
  refine ⟨C 2 * X + C c, 1, fun t _ => by simp, fun t _ => by simp; ring, ?_⟩
  have := natDegree_linear_le (a := (2:ℝ)) (b := c)
  simp only [natDegree_one, Nat.cast_zero, sub_zero]
  exact_mod_cast this

theorem aux_zz_Gamma_add_nat (s : ℝ) (hs : 0 < s) (m : ℕ) :
    Real.Gamma (s + m) = Real.Gamma s * ∏ i ∈ Finset.range m, (s + i) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, Nat.cast_succ, ← add_assoc,
      Real.Gamma_add_one (add_pos_of_pos_of_nonneg hs (Nat.cast_nonneg m)).ne', ih]
    ring

theorem aux_zz_natDegree_prod (a : ℝ) (m : ℕ) :
    (∏ i ∈ Finset.range m, (X + C (a + i))).natDegree = m := by
  rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_add_C _)]
  simp only [natDegree_X_add_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

theorem aux_zz_RD_up (a b : ℝ) (m : ℕ) (ha : 1 ≤ a) (hb : b = a + m) :
    aux_zz_RD (fun t => Real.Gamma (b + t) / Real.Gamma (a + t)) m := by
  refine ⟨∏ i ∈ Finset.range m, (X + C (a + i)), 1, fun t _ => by simp, ?_, ?_⟩
  · intro t ht
    have hpos : 0 < a + t := by linarith
    have hΓ : Real.Gamma (a + t) ≠ 0 := (Real.Gamma_pos_of_pos hpos).ne'
    have e : b + t = (a + t) + m := by rw [hb]; ring
    show Real.Gamma (b + t) / Real.Gamma (a + t) = _
    rw [e, aux_zz_Gamma_add_nat _ hpos, eval_one, div_one, eval_prod,
      mul_div_cancel_left₀ _ hΓ]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp only [eval_add, eval_X, eval_C]
    ring
  · rw [aux_zz_natDegree_prod]
    simp

theorem aux_zz_RD_down (a b : ℝ) (m : ℕ) (ha : 1 ≤ a) (hb : b = a + m) :
    aux_zz_RD (fun t => Real.Gamma (a + t) / Real.Gamma (b + t)) (-(m : ℤ)) := by
  refine ⟨1, ∏ i ∈ Finset.range m, (X + C (a + i)), ?_, ?_, ?_⟩
  · intro t ht
    rw [eval_prod]
    refine Finset.prod_ne_zero_iff.mpr (fun i _ => ?_)
    rw [eval_add, eval_X, eval_C]
    have : (0:ℝ) ≤ i := Nat.cast_nonneg i
    exact ne_of_gt (by linarith)
  · intro t ht
    have hpos : 0 < a + t := by linarith
    have hΓ : Real.Gamma (a + t) ≠ 0 := (Real.Gamma_pos_of_pos hpos).ne'
    have e : b + t = (a + t) + m := by rw [hb]; ring
    have hp : ∏ i ∈ Finset.range m, (a + t + (i : ℝ)) =
        ∏ i ∈ Finset.range m, eval t (X + C (a + i)) := by
      refine Finset.prod_congr rfl (fun i _ => ?_)
      simp only [eval_add, eval_X, eval_C]
      ring
    show Real.Gamma (a + t) / Real.Gamma (b + t) = _
    rw [e, aux_zz_Gamma_add_nat _ hpos, eval_one, eval_prod, ← hp,
      div_mul_cancel_left₀ hΓ, one_div]
  · rw [aux_zz_natDegree_prod]
    simp

theorem aux_zz_eta_mono (P : Params) (k : ℕ) :
    ∀ j, 1 ≤ j → j + k ≤ P.q → P.eta j ≤ P.eta (j + k) := by
  induction k with
  | zero => intro j _ _; simp
  | succ k ih =>
    intro j hj hjk
    have h1 := ih j hj (by omega)
    have h2 := P.eta_mono (j + k) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
    rw [← add_assoc]; exact h1.trans h2

theorem aux_zz_eta_le (P : Params) (j : ℕ) (hj : j ∈ Finset.Icc 1 P.q) :
    2 * P.eta j ≤ P.eta 0 := by
  rw [Finset.mem_Icc] at hj
  have := aux_zz_eta_mono P (P.q - j) j hj.1 (by omega)
  rw [show j + (P.q - j) = P.q by omega] at this
  have := P.eta_lt
  omega

theorem aux_zz_RD_R (P : Params) (n : ℕ) : aux_zz_RD (R P n) (-2) := by
  have hq := P.q_ge
  have hh0 : hh P n 0 = P.eta 0 * n + 2 := by simp [hh]
  have hhj : ∀ j, 1 ≤ j → hh P n j = P.eta j * n + 1 := fun j hj => by
    simp [hh, show j ≠ 0 by omega]
  have hle : ∀ j ∈ Finset.Icc 1 P.q, 2 * (P.eta j * n) ≤ P.eta 0 * n := fun j hj => by
    have := Nat.mul_le_mul_right n (aux_zz_eta_le P j hj)
    rw [mul_assoc] at this
    exact this
  have e1 : aux_zz_RD (fun t => (hh P n 0 : ℝ) + 2 * t) 1 := aux_zz_RD_lin _
  have e2 : aux_zz_RD (fun t => ∏ j ∈ Finset.Icc 1 P.r,
        (1 / (Nat.factorial (hh P n j - 1) : ℝ)) * Real.Gamma ((hh P n j : ℝ) + t)
          / Real.Gamma (1 + t)) (∑ j ∈ Finset.Icc 1 P.r, ((P.eta j * n : ℕ) : ℤ)) := by
    apply aux_zz_RD_prod
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have h := aux_zz_RD_mul (aux_zz_RD_const (1 / (Nat.factorial (hh P n j - 1) : ℝ)))
      (aux_zz_RD_up 1 (hh P n j : ℝ) (P.eta j * n) le_rfl
        (by rw [hhj j hj1]; push_cast; ring))
    exact aux_zz_RD_mono (aux_zz_RD_congr h (fun t _ => by simp only [mul_div_assoc]))
      (by simp)
  have e3 : aux_zz_RD (fun t => ∏ j ∈ Finset.Icc 1 P.r,
        (1 / (Nat.factorial (hh P n j - 1) : ℝ)) * Real.Gamma ((hh P n 0 : ℝ) + t)
          / Real.Gamma (1 + (hh P n 0 : ℝ) - (hh P n j : ℝ) + t))
        (∑ j ∈ Finset.Icc 1 P.r, ((P.eta j * n : ℕ) : ℤ)) := by
    apply aux_zz_RD_prod
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjq : j ∈ Finset.Icc 1 P.q :=
      Finset.mem_Icc.mpr ⟨hj1, by have := (Finset.mem_Icc.mp hj).2; omega⟩
    have hl := hle j hjq
    have hcast : (hh P n j : ℝ) ≤ (hh P n 0 : ℝ) := by
      rw [hh0, hhj j hj1]; exact_mod_cast (by omega)
    have h := aux_zz_RD_mul (aux_zz_RD_const (1 / (Nat.factorial (hh P n j - 1) : ℝ)))
      (aux_zz_RD_up (1 + (hh P n 0 : ℝ) - (hh P n j : ℝ)) (hh P n 0 : ℝ) (P.eta j * n)
        (by linarith) (by rw [hhj j hj1]; push_cast; ring))
    exact aux_zz_RD_mono (aux_zz_RD_congr h (fun t _ => by simp only [mul_div_assoc]))
      (by simp)
  have e4 : aux_zz_RD (fun t => ∏ j ∈ Finset.Icc (P.r + 1) P.q,
        (Nat.factorial (hh P n 0 - 2 * hh P n j) : ℝ) * Real.Gamma ((hh P n j : ℝ) + t)
          / Real.Gamma (1 + (hh P n 0 : ℝ) - (hh P n j : ℝ) + t))
        (∑ j ∈ Finset.Icc (P.r + 1) P.q,
          -(((1 + P.eta 0 * n - 2 * (P.eta j * n)) : ℕ) : ℤ)) := by
    apply aux_zz_RD_prod
    intro j hj
    have hj1 : 1 ≤ j := by have := (Finset.mem_Icc.mp hj).1; omega
    have hjq : j ∈ Finset.Icc 1 P.q := Finset.mem_Icc.mpr ⟨hj1, (Finset.mem_Icc.mp hj).2⟩
    have hl := hle j hjq
    have hm : (((1 + P.eta 0 * n - 2 * (P.eta j * n)) : ℕ) : ℝ) =
        1 + ((P.eta 0 * n : ℕ) : ℝ) - 2 * ((P.eta j * n : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have h := aux_zz_RD_mul (aux_zz_RD_const (Nat.factorial (hh P n 0 - 2 * hh P n j) : ℝ))
      (aux_zz_RD_down (hh P n j : ℝ) (1 + (hh P n 0 : ℝ) - (hh P n j : ℝ))
        (1 + P.eta 0 * n - 2 * (P.eta j * n))
        (by rw [hhj j hj1]; push_cast; have : (0:ℝ) ≤ (P.eta j : ℝ) * n := by positivity
            linarith)
        (by rw [hm, hh0, hhj j hj1]; push_cast; ring))
    exact aux_zz_RD_mono (aux_zz_RD_congr h (fun t _ => by simp only [mul_div_assoc]))
      (by simp)
  have e := aux_zz_RD_mul (aux_zz_RD_mul (aux_zz_RD_mul e1 e2) e3) e4
  refine aux_zz_RD_mono (aux_zz_RD_congr e (fun t _ => rfl)) ?_
  -- arithmetic
  have hT : (∑ j ∈ Finset.Icc (P.r + 1) P.q,
          -(((1 + P.eta 0 * n - 2 * (P.eta j * n)) : ℕ) : ℤ)) =
      ∑ j ∈ Finset.Icc (P.r + 1) P.q, (-(1 + (P.eta 0 : ℤ) * n) + 2 * n * (P.eta j : ℤ)) := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj1 : 1 ≤ j := by have := (Finset.mem_Icc.mp hj).1; omega
    have hjq : j ∈ Finset.Icc 1 P.q := Finset.mem_Icc.mpr ⟨hj1, (Finset.mem_Icc.mp hj).2⟩
    have hl := hle j hjq
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hS : (∑ j ∈ Finset.Icc 1 P.r, ((P.eta j * n : ℕ) : ℤ)) =
      (n : ℤ) * ∑ j ∈ Finset.Icc 1 P.r, (P.eta j : ℤ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    push_cast; ring
  rw [hT, hS, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, ← Finset.mul_sum]
  have hsplit : ∑ j ∈ Finset.Icc 1 P.r, P.eta j + ∑ j ∈ Finset.Icc (P.r + 1) P.q, P.eta j =
      ∑ j ∈ Finset.Icc 1 P.q, P.eta j := by
    rw [← Finset.Ico_add_one_right_eq_Icc, ← Finset.Ico_add_one_right_eq_Icc,
      ← Finset.Ico_add_one_right_eq_Icc,
      Finset.sum_Ico_consecutive _ (by omega) (by omega)]
  have hsum := P.sum_le
  rw [← hsplit] at hsum
  have hsum' := Nat.mul_le_mul_right n hsum
  have hsumZ : ((2 * (∑ j ∈ Finset.Icc 1 P.r, P.eta j +
      ∑ j ∈ Finset.Icc (P.r + 1) P.q, P.eta j) * n : ℕ) : ℤ) ≤
      ((P.eta 0 * (P.q - P.r) * n : ℕ) : ℤ) := by exact_mod_cast hsum'
  have hcard : P.q + 1 - (P.r + 1) = P.q - P.r := by omega
  rw [hcard]
  push_cast [nsmul_eq_mul, Nat.cast_sub (show P.r ≤ P.q by omega)] at hsumZ ⊢
  have hqr : (4 : ℤ) ≤ (P.q : ℤ) - P.r := by
    have : P.r + 4 ≤ P.q := hq
    omega
  linarith


theorem rational_function_decay (P : Params) (n : ℕ) :
    Tendsto (R P n) atTop (𝓝 0) ∧
      Tendsto (fun t : ℝ => t * R P n t) atTop (𝓝 0) := by
  obtain ⟨A, B, hB, hR, hd⟩ := aux_zz_RD_R P n
  have hB0 : B ≠ 0 := by
    intro hz
    exact hB 0 (by norm_num) (by simp [hz])
  have hnat : A.natDegree + 2 ≤ B.natDegree := by omega
  have hdeg : A.degree < B.degree := by
    rw [degree_eq_natDegree hB0]
    apply degree_le_natDegree.trans_lt
    exact_mod_cast (show A.natDegree < B.natDegree by omega)
  have hdegX : ((X : ℝ[X]) * A).degree < B.degree := by
    rw [degree_eq_natDegree hB0]
    apply degree_le_natDegree.trans_lt
    have h := natDegree_mul_le (p := (X : ℝ[X])) (q := A)
    rw [natDegree_X] at h
    exact_mod_cast (show ((X : ℝ[X]) * A).natDegree < B.natDegree by omega)
  constructor
  · apply (div_tendsto_atTop_zero_of_degree_lt A B hdeg).congr'
    filter_upwards [eventually_gt_atTop (-1 : ℝ)] with t ht
    exact (hR t ht).symm
  · have h := div_tendsto_atTop_zero_of_degree_lt ((X : ℝ[X]) * A) B hdegX
    apply h.congr'
    filter_upwards [eventually_gt_atTop (-1 : ℝ)] with t ht
    rw [eval_mul, eval_X, hR t ht]
    ring

end ZudilinZeta
end


-- Source module: missions.zudilin.RationalModelTest
section
set_option autoImplicit false

namespace ZudilinZeta

open Polynomial Finset Filter
open scoped Topology

noncomputable def pfInterval (a b : ℕ) : ℚ[X] := ∏ k ∈ Ico a b, (X + C (k : ℚ))

noncomputable def pfNumerator (P : Params) (n : ℕ) : ℚ[X] :=
  (C (hh P n 0 : ℚ) + C 2 * X) *
    (∏ j ∈ Icc 1 P.r, C (1 / ((hh P n j - 1).factorial : ℚ)) *
      pfInterval 1 (hh P n j)) *
    (∏ j ∈ Icc 1 P.r, C (1 / ((hh P n j - 1).factorial : ℚ)) *
      pfInterval (hh P n 0 + 1 - hh P n j) (hh P n 0)) *
    (∏ j ∈ Icc (P.r+1) P.q, C ((hh P n 0 - 2 * hh P n j).factorial : ℚ))

noncomputable def pfDenominator (P : Params) (n : ℕ) : ℚ[X] :=
  ∏ j ∈ Icc (P.r+1) P.q, pfInterval (hh P n j) (hh P n 0 + 1 - hh P n j)

lemma pfInterval_eval (a b : ℕ) (t : ℝ) :
    (pfInterval a b).eval₂ (algebraMap ℚ ℝ) t = ∏ k ∈ Ico a b, (t + (k : ℝ)) := by
  simp [pfInterval, eval₂_finsetProd]

lemma pfInterval_reflect (a b H : ℕ) (hb : b ≤ H+1) (t : ℝ) :
    (pfInterval a b).eval₂ (algebraMap ℚ ℝ) (-(H : ℝ)-t) =
      (-1 : ℝ)^(b-a) * (pfInterval (H+1-b) (H+1-a)).eval₂ (algebraMap ℚ ℝ) t := by
  simp only [pfInterval_eval]
  have he : (∏ k ∈ Ico a b, (-(H : ℝ)-t+(k : ℝ))) =
      ∏ k ∈ Ico a b, -(t+(H-k : ℕ)) := by
    apply prod_congr rfl
    intro k hk
    have hkle : k ≤ H := by have := (mem_Ico.mp hk).2; omega
    rw [Nat.cast_sub hkle]
    ring
  rw [he, Finset.prod_neg, Nat.card_Ico]
  congr 1
  exact prod_Ico_reflect (fun k : ℕ => t+(k : ℝ)) a (n := H) hb

lemma pf_hh_bounds (P : Params) (n j : ℕ) (hj : j ∈ Icc 1 P.q) :
    0 < hh P n j ∧ 2 * hh P n j ≤ hh P n 0 := by
  have hle := Nat.mul_le_mul_right n (aux_zz_eta_le P j hj)
  have hj0 : j ≠ 0 := by have := (mem_Icc.mp hj).1; omega
  have he0 : hh P n 0 = P.eta 0*n+2 := by simp [hh]
  have hej : hh P n j = P.eta j*n+1 := by simp [hh, hj0]
  rw [he0, hej]
  rw [mul_assoc] at hle
  omega

lemma pf_gamma_quotient (a b : ℕ) (ha : 0 < a) (hab : a ≤ b)
    (t : ℝ) (ht : -1 < t) :
    Real.Gamma ((b : ℝ)+t) / Real.Gamma ((a : ℝ)+t) =
      (pfInterval a b).eval₂ (algebraMap ℚ ℝ) t := by
  have hapos : 0 < (a : ℝ)+t := by
    have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
    linarith
  have hb : (b : ℝ)+t = ((a : ℝ)+t) + (b-a : ℕ) := by
    rw [Nat.cast_sub hab]
    ring
  rw [hb, aux_zz_Gamma_add_nat _ hapos,
    mul_div_cancel_left₀ _ (Real.Gamma_pos_of_pos hapos).ne']
  simp only [pfInterval, eval₂_finsetProd, eval₂_add, eval₂_X, eval₂_C, map_natCast, eval₂_natCast]
  rw [prod_Ico_eq_prod_range]
  apply prod_congr rfl
  intro i hi
  push_cast
  ring

lemma pf_gamma_inverse_quotient (a b : ℕ) (ha : 0 < a) (hab : a ≤ b)
    (t : ℝ) (ht : -1 < t) :
    Real.Gamma ((a : ℝ)+t) / Real.Gamma ((b : ℝ)+t) =
      1 / (pfInterval a b).eval₂ (algebraMap ℚ ℝ) t := by
  rw [← pf_gamma_quotient a b ha hab t ht, one_div, inv_div]

lemma pf_real_expansion (P : Params) (n : ℕ) (t : ℝ) (ht : -1 < t) :
    R P n t = (pfNumerator P n).eval₂ (algebraMap ℚ ℝ) t /
      (pfDenominator P n).eval₂ (algebraMap ℚ ℝ) t := by
  have hqr := P.q_ge
  have hreal (j : ℕ) (hj : j ∈ Icc 1 P.q) :
      ((hh P n 0 + 1 - hh P n j : ℕ) : ℝ) = 1 + (hh P n 0 : ℝ) - hh P n j := by
    have hb := pf_hh_bounds P n j hj
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have h1 (j : ℕ) (hj : j ∈ Icc 1 P.r) :
      Real.Gamma ((hh P n j : ℝ)+t) / Real.Gamma (1+t) =
        (pfInterval 1 (hh P n j)).eval₂ (algebraMap ℚ ℝ) t := by
    have hjq : j ∈ Icc 1 P.q := mem_Icc.mpr ⟨(mem_Icc.mp hj).1, by have := (mem_Icc.mp hj).2; omega⟩
    simpa only [Nat.cast_one] using pf_gamma_quotient 1 (hh P n j) (by omega)
      (pf_hh_bounds P n j hjq).1 t ht
  have h2 (j : ℕ) (hj : j ∈ Icc 1 P.r) :
      Real.Gamma ((hh P n 0 : ℝ)+t) / Real.Gamma (1+(hh P n 0 : ℝ)-hh P n j+t) =
        (pfInterval (hh P n 0+1-hh P n j) (hh P n 0)).eval₂ (algebraMap ℚ ℝ) t := by
    have hjq : j ∈ Icc 1 P.q := mem_Icc.mpr ⟨(mem_Icc.mp hj).1, by have := (mem_Icc.mp hj).2; omega⟩
    have hb := pf_hh_bounds P n j hjq
    simpa only [hreal j hjq] using pf_gamma_quotient (hh P n 0+1-hh P n j) (hh P n 0)
      (by omega) (by omega) t ht
  have h3 (j : ℕ) (hj : j ∈ Icc (P.r+1) P.q) :
      Real.Gamma ((hh P n j : ℝ)+t) / Real.Gamma (1+(hh P n 0 : ℝ)-hh P n j+t) =
        1 / (pfInterval (hh P n j) (hh P n 0+1-hh P n j)).eval₂ (algebraMap ℚ ℝ) t := by
    have hjq : j ∈ Icc 1 P.q := mem_Icc.mpr ⟨by have := (mem_Icc.mp hj).1; omega, (mem_Icc.mp hj).2⟩
    have hb := pf_hh_bounds P n j hjq
    simpa only [hreal j hjq] using pf_gamma_inverse_quotient (hh P n j) (hh P n 0+1-hh P n j)
      hb.1 (by omega) t ht
  simp only [R, pfNumerator, pfDenominator, eval₂_mul, eval₂_add, eval₂_X,
    eval₂_C, eval₂_finsetProd, map_div₀, map_one, map_natCast, map_ofNat, eval₂_natCast, eval₂_ofNat, mul_div_assoc]
  have e1 := prod_congr rfl (fun j hj => congrArg (fun x : ℝ =>
    (1 / ((hh P n j-1).factorial : ℝ))*x) (h1 j hj))
  have e2 := prod_congr rfl (fun j hj => congrArg (fun x : ℝ =>
    (1 / ((hh P n j-1).factorial : ℝ))*x) (h2 j hj))
  have e3 := prod_congr rfl (fun j hj => congrArg (fun x : ℝ =>
    ((hh P n 0-2*hh P n j).factorial : ℝ)*x) (h3 j hj))
  rw [e1, e2, e3]
  simp only [mul_one_div, prod_div_distrib]

lemma pfNumerator_eval (P : Params) (n : ℕ) (t : ℝ) :
    (pfNumerator P n).eval₂ (algebraMap ℚ ℝ) t =
      ((hh P n 0 : ℝ)+2*t) *
      (∏ j ∈ Icc 1 P.r, (1 / ((hh P n j-1).factorial : ℝ))^2 *
        (pfInterval 1 (hh P n j)).eval₂ (algebraMap ℚ ℝ) t *
        (pfInterval (hh P n 0+1-hh P n j) (hh P n 0)).eval₂ (algebraMap ℚ ℝ) t) *
      (∏ j ∈ Icc (P.r+1) P.q, ((hh P n 0-2*hh P n j).factorial : ℝ)) := by
  simp only [pfNumerator, eval₂_mul, eval₂_add, eval₂_X, eval₂_C, eval₂_finsetProd,
    map_div₀, map_one, map_natCast, eval₂_natCast, eval₂_ofNat, map_ofNat]
  rw [mul_assoc ((hh P n 0 : ℝ)+2*t), ← prod_mul_distrib]
  congr 2
  apply prod_congr rfl
  intro j hj
  ring

lemma pfNumerator_reflect (P : Params) (n : ℕ) (t : ℝ) :
    (pfNumerator P n).eval₂ (algebraMap ℚ ℝ) (-(hh P n 0 : ℝ)-t) =
      -(pfNumerator P n).eval₂ (algebraMap ℚ ℝ) t := by
  have hqr := P.q_ge
  have hpair (j : ℕ) (hj : j ∈ Icc 1 P.r) :
      (pfInterval 1 (hh P n j)).eval₂ (algebraMap ℚ ℝ) (-(hh P n 0 : ℝ)-t) *
      (pfInterval (hh P n 0+1-hh P n j) (hh P n 0)).eval₂ (algebraMap ℚ ℝ) (-(hh P n 0 : ℝ)-t) =
      (pfInterval 1 (hh P n j)).eval₂ (algebraMap ℚ ℝ) t *
      (pfInterval (hh P n 0+1-hh P n j) (hh P n 0)).eval₂ (algebraMap ℚ ℝ) t := by
    have hjq : j ∈ Icc 1 P.q := mem_Icc.mpr ⟨(mem_Icc.mp hj).1, by have := (mem_Icc.mp hj).2; omega⟩
    have hb := pf_hh_bounds P n j hjq
    rw [pfInterval_reflect _ _ _ (by omega), pfInterval_reflect _ _ _ (by omega)]
    have e1 : hh P n 0+1-1 = hh P n 0 := by omega
    have e2 : hh P n 0+1-hh P n 0 = 1 := by omega
    have e3 : hh P n 0+1-(hh P n 0+1-hh P n j) = hh P n j := by omega
    have e4 : hh P n 0-(hh P n 0+1-hh P n j) = hh P n j-1 := by omega
    rw [e1, e2, e3, e4]
    have hs : ((-1 : ℝ)^(hh P n j-1))^2 = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    linear_combination
      ((pfInterval 1 (hh P n j)).eval₂ (algebraMap ℚ ℝ) t *
       (pfInterval (hh P n 0+1-hh P n j) (hh P n 0)).eval₂ (algebraMap ℚ ℝ) t) * hs
  simp only [pfNumerator_eval]
  have hp : (∏ j ∈ Icc 1 P.r, (1 / ((hh P n j-1).factorial : ℝ))^2 *
      (pfInterval 1 (hh P n j)).eval₂ (algebraMap ℚ ℝ) (-(hh P n 0 : ℝ)-t) *
      (pfInterval (hh P n 0+1-hh P n j) (hh P n 0)).eval₂ (algebraMap ℚ ℝ) (-(hh P n 0 : ℝ)-t)) =
      ∏ j ∈ Icc 1 P.r, (1 / ((hh P n j-1).factorial : ℝ))^2 *
      (pfInterval 1 (hh P n j)).eval₂ (algebraMap ℚ ℝ) t *
      (pfInterval (hh P n 0+1-hh P n j) (hh P n 0)).eval₂ (algebraMap ℚ ℝ) t := by
    apply prod_congr rfl
    intro j hj
    rw [mul_assoc, hpair j hj, ← mul_assoc]
  rw [hp]
  ring

lemma pfDenominator_reflect (P : Params) (n : ℕ) (t : ℝ) :
    (pfDenominator P n).eval₂ (algebraMap ℚ ℝ) (-(hh P n 0 : ℝ)-t) =
      (pfDenominator P n).eval₂ (algebraMap ℚ ℝ) t := by
  have hj (j : ℕ) (hj : j ∈ Icc (P.r+1) P.q) :
      (pfInterval (hh P n j) (hh P n 0+1-hh P n j)).eval₂ (algebraMap ℚ ℝ) (-(hh P n 0 : ℝ)-t) =
      (-1 : ℝ)^(hh P n 0+1) *
        (pfInterval (hh P n j) (hh P n 0+1-hh P n j)).eval₂ (algebraMap ℚ ℝ) t := by
    have hjq : j ∈ Icc 1 P.q := mem_Icc.mpr ⟨by have := (mem_Icc.mp hj).1; omega, (mem_Icc.mp hj).2⟩
    have hb := pf_hh_bounds P n j hjq
    rw [pfInterval_reflect _ _ _ (by omega)]
    have he : hh P n 0+1-(hh P n 0+1-hh P n j) = hh P n j := by omega
    rw [he]
    congr 1
    have he : (hh P n 0+1-hh P n j)-hh P n j + 2*hh P n j = hh P n 0+1 := by omega
    have hpow := congrArg (fun e : ℕ => (-1 : ℝ)^e) he
    rw [pow_add, (even_two.mul_right (hh P n j)).neg_one_pow, mul_one] at hpow
    exact hpow
  simp only [pfDenominator, eval₂_finsetProd]
  rw [prod_congr rfl hj, prod_mul_distrib, prod_const, Nat.card_Icc]
  have hc : P.q+1-(P.r+1) = P.q-P.r := by omega
  rw [hc]
  have hp : ((-1 : ℝ)^(hh P n 0+1))^(P.q-P.r) = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, (Nat.Odd.sub_odd P.q_odd P.r_odd).neg_one_pow, one_pow]
  rw [hp, one_mul]

lemma pfDenominator_dvd_uniform (P : Params) (n : ℕ) :
    pfDenominator P n ∣ ∏ k ∈ poleRange P n, (X + C (k : ℚ))^(P.q-P.r) := by
  have hqr := P.q_ge
  have hsub (j : ℕ) (hj : j ∈ Icc (P.r+1) P.q) :
      Ico (hh P n j) (hh P n 0+1-hh P n j) ⊆ poleRange P n := by
    have hjq : j ∈ Icc 1 P.q := mem_Icc.mpr ⟨by have := (mem_Icc.mp hj).1; omega, (mem_Icc.mp hj).2⟩
    have hb := pf_hh_bounds P n j hjq
    have hmono := aux_zz_eta_mono P (j-(P.r+1)) (P.r+1) (by omega) (by have := (mem_Icc.mp hj).2; omega)
    have he : P.r+1+(j-(P.r+1)) = j := by have := (mem_Icc.mp hj).1; omega
    rw [he] at hmono
    have hm := Nat.mul_le_mul_right n hmono
    have hlow : hh P n (P.r+1) ≤ hh P n j := by
      simp only [hh, if_neg (show P.r+1 ≠ 0 by omega), if_neg (show j ≠ 0 by have := (mem_Icc.mp hj).1; omega)]
      omega
    intro k hk
    apply mem_Icc.mpr
    have hk' := mem_Ico.mp hk
    omega
  have hd (j : ℕ) (hj : j ∈ Icc (P.r+1) P.q) :
      pfInterval (hh P n j) (hh P n 0+1-hh P n j) ∣
        ∏ k ∈ poleRange P n, (X + C (k : ℚ)) :=
    prod_dvd_prod_of_subset _ _ _ (hsub j hj)
  have h := prod_dvd_prod_of_dvd
    (fun j => pfInterval (hh P n j) (hh P n 0+1-hh P n j))
    (fun _ => ∏ k ∈ poleRange P n, (X + C (k : ℚ))) hd
  have hc : P.q+1-(P.r+1) = P.q-P.r := by omega
  simpa only [pfDenominator, prod_const, Nat.card_Icc, hc, prod_pow] using h

lemma pf_uniform_model (P : Params) (n : ℕ) :
    ∃ A : ℚ[X], ∀ t : ℝ, (∀ k ∈ poleRange P n, t+(k : ℝ) ≠ 0) →
      A.eval₂ (algebraMap ℚ ℝ) t / (∏ k ∈ poleRange P n, (t+(k : ℝ))^(P.q-P.r)) =
        (pfNumerator P n).eval₂ (algebraMap ℚ ℝ) t /
          (pfDenominator P n).eval₂ (algebraMap ℚ ℝ) t := by
  obtain ⟨B, hB⟩ := pfDenominator_dvd_uniform P n
  refine ⟨pfNumerator P n * B, ?_⟩
  intro t ht
  have hn : (∏ k ∈ poleRange P n, (t+(k : ℝ))^(P.q-P.r)) ≠ 0 :=
    prod_ne_zero_iff.mpr (fun k hk => pow_ne_zero _ (ht k hk))
  have he := congrArg (fun p : ℚ[X] => p.eval₂ (algebraMap ℚ ℝ) t) hB
  simp only [eval₂_finsetProd, eval₂_pow, eval₂_mul, eval₂_add, eval₂_X, eval₂_C,
    map_natCast, eval₂_natCast] at he
  have hB0 : B.eval₂ (algebraMap ℚ ℝ) t ≠ 0 := by
    intro hz
    apply hn
    rw [he, hz, mul_zero]
  rw [eval₂_mul, he, mul_div_mul_right _ _ hB0]

end ZudilinZeta
end


-- Source module: missions.zudilin.ComplexRationalModel
section
set_option autoImplicit false
noncomputable section
open Complex Polynomial Finset Filter Topology

namespace ZudilinZeta

def complexRationalR (P : Params) (n : ℕ) (z : ℂ) : ℂ :=
  (pfNumerator P n).eval₂ (algebraMap ℚ ℂ) z /
    (pfDenominator P n).eval₂ (algebraMap ℚ ℂ) z

lemma polynomial_eval₂_complex_ofReal (p : ℚ[X]) (t : ℝ) :
    p.eval₂ (algebraMap ℚ ℂ) (t : ℂ) = ((p.eval₂ (algebraMap ℚ ℝ) t : ℝ) : ℂ) := by
  have he : Complex.ofRealHom.comp (algebraMap ℚ ℝ) = algebraMap ℚ ℂ :=
    Subsingleton.elim _ _
  simpa only [he, Complex.ofRealHom_eq_coe] using
    (Polynomial.hom_eval₂ p (algebraMap ℚ ℝ) Complex.ofRealHom t).symm

lemma complexRationalR_ofReal (P : Params) (n : ℕ) (t : ℝ) (ht : -1 < t) :
    complexRationalR P n (t : ℂ) = (R P n t : ℂ) := by
  rw [pf_real_expansion P n t ht]
  simp only [complexRationalR, polynomial_eval₂_complex_ofReal, Complex.ofReal_div]

lemma polynomial_reflection_lift (p : ℚ[X]) (H : ℕ) (s : ℚ)
    (h : ∀ t : ℝ, p.eval₂ (algebraMap ℚ ℝ) (-(H : ℝ) - t) =
      (s : ℝ) * p.eval₂ (algebraMap ℚ ℝ) t) (z : ℂ) :
    p.eval₂ (algebraMap ℚ ℂ) (-(H : ℂ) - z) =
      (s : ℂ) * p.eval₂ (algebraMap ℚ ℂ) z := by
  have hp : p.comp (-C (H : ℚ) - X) = C s * p := by
    apply Polynomial.map_injective (algebraMap ℚ ℝ) (Rat.cast_injective (α := ℝ))
    apply Polynomial.funext
    intro t
    simpa [Polynomial.eval_map, Polynomial.eval₂_comp] using h t
  have he := congrArg (fun q : ℚ[X] => q.eval₂ (algebraMap ℚ ℂ) z) hp
  simpa [Polynomial.eval₂_comp] using he

lemma pfNumerator_reflect_complex (P : Params) (n : ℕ) (z : ℂ) :
    (pfNumerator P n).eval₂ (algebraMap ℚ ℂ) (-(hh P n 0 : ℂ) - z) =
      -(pfNumerator P n).eval₂ (algebraMap ℚ ℂ) z := by
  simpa using polynomial_reflection_lift (pfNumerator P n) (hh P n 0) (-1)
    (by simpa using pfNumerator_reflect P n) z

lemma pfDenominator_reflect_complex (P : Params) (n : ℕ) (z : ℂ) :
    (pfDenominator P n).eval₂ (algebraMap ℚ ℂ) (-(hh P n 0 : ℂ) - z) =
      (pfDenominator P n).eval₂ (algebraMap ℚ ℂ) z := by
  simpa using polynomial_reflection_lift (pfDenominator P n) (hh P n 0) 1
    (by simpa using pfDenominator_reflect P n) z

lemma complexRationalR_reflect (P : Params) (n : ℕ) (z : ℂ) :
    complexRationalR P n (-(hh P n 0 : ℂ) - z) = -complexRationalR P n z := by
  simp only [complexRationalR, pfNumerator_reflect_complex,
    pfDenominator_reflect_complex, neg_div]

lemma complexRationalR_second_reflect (P : Params) (n : ℕ) (z : ℂ) :
    iteratedDeriv 2 (complexRationalR P n) (-(hh P n 0 : ℂ) - z) =
      -iteratedDeriv 2 (complexRationalR P n) z := by
  have he : (fun w : ℂ => complexRationalR P n (-(hh P n 0 : ℂ) - w)) =
      fun w => -complexRationalR P n w := by
    funext w
    exact complexRationalR_reflect P n w
  have hd := congrArg (fun f : ℂ → ℂ => iteratedDeriv 2 f z) he
  simpa only [iteratedDeriv_comp_const_sub, neg_one_sq, one_smul,
    iteratedDeriv_fun_neg] using hd

lemma pfInterval_eval_complex (a b : ℕ) (z : ℂ) :
    (pfInterval a b).eval₂ (algebraMap ℚ ℂ) z = ∏ k ∈ Ico a b, (z + (k : ℂ)) := by
  simp [pfInterval, eval₂_finsetProd]

lemma pfDenominator_nonzero_complex (P : Params) (n : ℕ) (z : ℂ)
    (hz : ∀ j ∈ Icc (P.r + 1) P.q, ∀ k ∈ Ico (hh P n j) (hh P n 0 + 1 - hh P n j),
      z + (k : ℂ) ≠ 0) :
    (pfDenominator P n).eval₂ (algebraMap ℚ ℂ) z ≠ 0 := by
  simp only [pfDenominator, eval₂_finsetProd, pfInterval_eval_complex]
  exact prod_ne_zero_iff.mpr (fun j hj => prod_ne_zero_iff.mpr (hz j hj))

lemma analyticAt_complexRationalR (P : Params) (n : ℕ) (z : ℂ)
    (hz : (pfDenominator P n).eval₂ (algebraMap ℚ ℂ) z ≠ 0) :
    AnalyticAt ℂ (complexRationalR P n) z := by
  exact (analyticAt_id.aeval_polynomial (pfNumerator P n)).div
    (analyticAt_id.aeval_polynomial (pfDenominator P n)) hz

lemma pfDenominator_nonzero_right (P : Params) (n : ℕ) (z : ℂ) (hz : -1 < z.re) :
    (pfDenominator P n).eval₂ (algebraMap ℚ ℂ) z ≠ 0 := by
  apply pfDenominator_nonzero_complex P n z
  intro j hj k hk he
  have hjq : j ∈ Icc 1 P.q := by
    have := mem_Icc.mp hj
    exact mem_Icc.mpr ⟨by omega, this.2⟩
  have hkpos : 0 < k := lt_of_lt_of_le (pf_hh_bounds P n j hjq).1 (mem_Ico.mp hk).1
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hkpos
  have hre := congrArg Complex.re he
  simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at hre
  linarith

lemma pfDenominator_nonzero_left (P : Params) (n : ℕ) (z : ℂ)
    (hz : z.re < -(hh P n 0 : ℝ) + 1) :
    (pfDenominator P n).eval₂ (algebraMap ℚ ℂ) z ≠ 0 := by
  have hleft : -1 < (-(hh P n 0 : ℂ) - z).re := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re]
    linarith
  simpa only [pfDenominator_reflect_complex] using
    pfDenominator_nonzero_right P n (-(hh P n 0 : ℂ) - z) hleft

end ZudilinZeta
end
end


-- Source module: missions.zudilin.ComplexGammaQuotients
section
set_option autoImplicit false
noncomputable section
open Complex Polynomial Finset

namespace ZudilinZeta

lemma gamma_ne_zero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) : Complex.Gamma z ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro k he
  apply hz
  simpa only [Complex.neg_im, Complex.natCast_im, neg_zero] using congrArg Complex.im he

lemma gamma_add_nat_of_im_ne_zero (z : ℂ) (hz : z.im ≠ 0) (m : ℕ) :
    Complex.Gamma (z + m) = Complex.Gamma z * ∏ i ∈ range m, (z + (i : ℂ)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hne : z + (m : ℂ) ≠ 0 := by
      intro he
      apply hz
      simpa using congrArg Complex.im he
    rw [prod_range_succ, Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ hne, ih]
    ring

lemma pf_gamma_quotient_complex (a b : ℕ) (hab : a ≤ b) (z : ℂ) (hz : z.im ≠ 0) :
    Complex.Gamma ((b : ℂ) + z) / Complex.Gamma ((a : ℂ) + z) =
      (pfInterval a b).eval₂ (algebraMap ℚ ℂ) z := by
  have ha : ((a : ℂ) + z).im ≠ 0 := by simpa using hz
  have hb : (b : ℂ) + z = ((a : ℂ) + z) + (b - a : ℕ) := by
    rw [Nat.cast_sub hab]
    ring
  rw [hb, gamma_add_nat_of_im_ne_zero _ ha,
    mul_div_cancel_left₀ _ (gamma_ne_zero_of_im_ne_zero ha), pfInterval_eval_complex,
    prod_Ico_eq_prod_range]
  apply prod_congr rfl
  intro i hi
  push_cast
  ring

lemma pf_gamma_inverse_quotient_complex (a b : ℕ) (hab : a ≤ b) (z : ℂ) (hz : z.im ≠ 0) :
    Complex.Gamma ((a : ℂ) + z) / Complex.Gamma ((b : ℂ) + z) =
      1 / (pfInterval a b).eval₂ (algebraMap ℚ ℂ) z := by
  rw [← pf_gamma_quotient_complex a b hab z hz, one_div, inv_div]

end ZudilinZeta
end
end


-- Source module: missions.zudilin.ComplexGammaModel
section
set_option autoImplicit false
noncomputable section
open Complex Polynomial Finset
namespace ZudilinZeta

-- Complex continuation of the existing Gamma-quotient calculation in RationalModelTest.
def complexGammaR (P : Params) (n : ℕ) (t : ℂ) : ℂ :=
  ((hh P n 0 : ℂ) + 2 * t)
    * (∏ j ∈ Finset.Icc 1 P.r,
        (1 / (Nat.factorial (hh P n j - 1) : ℂ)) * Complex.Gamma ((hh P n j : ℂ) + t)
          / Complex.Gamma (1 + t))
    * (∏ j ∈ Finset.Icc 1 P.r,
        (1 / (Nat.factorial (hh P n j - 1) : ℂ)) * Complex.Gamma ((hh P n 0 : ℂ) + t)
          / Complex.Gamma (1 + (hh P n 0 : ℂ) - (hh P n j : ℂ) + t))
    * (∏ j ∈ Finset.Icc (P.r + 1) P.q,
        (Nat.factorial (hh P n 0 - 2 * hh P n j) : ℂ) * Complex.Gamma ((hh P n j : ℂ) + t)
          / Complex.Gamma (1 + (hh P n 0 : ℂ) - (hh P n j : ℂ) + t))

lemma complexGammaR_expansion (P : Params) (n : ℕ) (t : ℂ) (ht : t.im ≠ 0) :
    complexGammaR P n t = (pfNumerator P n).eval₂ (algebraMap ℚ ℂ) t /
      (pfDenominator P n).eval₂ (algebraMap ℚ ℂ) t := by
  have hquot (a b : ℕ) (_ha : 0 < a) (hab : a ≤ b) (z : ℂ) (hz : z.im ≠ 0) :=
    pf_gamma_quotient_complex a b hab z hz
  have hinv (a b : ℕ) (_ha : 0 < a) (hab : a ≤ b) (z : ℂ) (hz : z.im ≠ 0) :=
    pf_gamma_inverse_quotient_complex a b hab z hz
  have hqr := P.q_ge
  have hreal (j : ℕ) (hj : j ∈ Icc 1 P.q) :
      ((hh P n 0 + 1 - hh P n j : ℕ) : ℂ) = 1 + (hh P n 0 : ℂ) - hh P n j := by
    have hb := pf_hh_bounds P n j hj
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have h1 (j : ℕ) (hj : j ∈ Icc 1 P.r) :
      Complex.Gamma ((hh P n j : ℂ)+t) / Complex.Gamma (1+t) =
        (pfInterval 1 (hh P n j)).eval₂ (algebraMap ℚ ℂ) t := by
    have hjq : j ∈ Icc 1 P.q := mem_Icc.mpr ⟨(mem_Icc.mp hj).1, by have := (mem_Icc.mp hj).2; omega⟩
    simpa only [Nat.cast_one] using hquot 1 (hh P n j) (by omega)
      (pf_hh_bounds P n j hjq).1 t ht
  have h2 (j : ℕ) (hj : j ∈ Icc 1 P.r) :
      Complex.Gamma ((hh P n 0 : ℂ)+t) / Complex.Gamma (1+(hh P n 0 : ℂ)-hh P n j+t) =
        (pfInterval (hh P n 0+1-hh P n j) (hh P n 0)).eval₂ (algebraMap ℚ ℂ) t := by
    have hjq : j ∈ Icc 1 P.q := mem_Icc.mpr ⟨(mem_Icc.mp hj).1, by have := (mem_Icc.mp hj).2; omega⟩
    have hb := pf_hh_bounds P n j hjq
    simpa only [hreal j hjq] using hquot (hh P n 0+1-hh P n j) (hh P n 0)
      (by omega) (by omega) t ht
  have h3 (j : ℕ) (hj : j ∈ Icc (P.r+1) P.q) :
      Complex.Gamma ((hh P n j : ℂ)+t) / Complex.Gamma (1+(hh P n 0 : ℂ)-hh P n j+t) =
        1 / (pfInterval (hh P n j) (hh P n 0+1-hh P n j)).eval₂ (algebraMap ℚ ℂ) t := by
    have hjq : j ∈ Icc 1 P.q := mem_Icc.mpr ⟨by have := (mem_Icc.mp hj).1; omega, (mem_Icc.mp hj).2⟩
    have hb := pf_hh_bounds P n j hjq
    simpa only [hreal j hjq] using hinv (hh P n j) (hh P n 0+1-hh P n j)
      hb.1 (by omega) t ht
  simp only [complexGammaR, pfNumerator, pfDenominator, eval₂_mul, eval₂_add, eval₂_X,
    eval₂_C, eval₂_finsetProd, map_div₀, map_one, map_natCast, map_ofNat, eval₂_natCast, eval₂_ofNat, mul_div_assoc]
  have e1 := prod_congr rfl (fun j hj => congrArg (fun x : ℂ =>
    (1 / ((hh P n j-1).factorial : ℂ))*x) (h1 j hj))
  have e2 := prod_congr rfl (fun j hj => congrArg (fun x : ℂ =>
    (1 / ((hh P n j-1).factorial : ℂ))*x) (h2 j hj))
  have e3 := prod_congr rfl (fun j hj => congrArg (fun x : ℂ =>
    ((hh P n 0-2*hh P n j).factorial : ℂ)*x) (h3 j hj))
  rw [e1, e2, e3]
  simp only [mul_one_div, prod_div_distrib]

end ZudilinZeta
end
end


-- Source module: missions.zudilin.ComplexGammaReflection
section
set_option autoImplicit false
noncomputable section
open Complex

namespace ZudilinZeta

lemma sin_pi_mul_ne_zero_of_im {z : ℂ} (hz : z.im ≠ 0) :
    Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
  rw [Complex.sin_ne_zero_iff]
  intro k he
  apply mul_ne_zero Real.pi_ne_zero hz
  simpa [Complex.mul_im] using congrArg Complex.im he

lemma gamma_ratio_reflect {a b : ℂ} (ha : a.im ≠ 0) (hb : b.im ≠ 0) :
    Complex.Gamma a / Complex.Gamma b =
      (Complex.sin ((Real.pi : ℂ) * b) / Complex.sin ((Real.pi : ℂ) * a)) *
        (Complex.Gamma (1 - b) / Complex.Gamma (1 - a)) := by
  have hsa := sin_pi_mul_ne_zero_of_im ha
  have hsb := sin_pi_mul_ne_zero_of_im hb
  have hgb := gamma_ne_zero_of_im_ne_zero hb
  have hga := gamma_ne_zero_of_im_ne_zero (z := 1 - a) (by simpa using ha)
  have hea := (eq_div_iff hsa).mp (Complex.Gamma_mul_Gamma_one_sub a)
  have heb := (eq_div_iff hsb).mp (Complex.Gamma_mul_Gamma_one_sub b)
  field_simp
  linear_combination hea - heb

lemma inv_gamma_one_sub {z : ℂ} (hz : z.im ≠ 0) :
    (Complex.Gamma (1 - z))⁻¹ =
      Complex.Gamma z * Complex.sin ((Real.pi : ℂ) * z) / (Real.pi : ℂ) := by
  have hs := sin_pi_mul_ne_zero_of_im hz
  have hg := gamma_ne_zero_of_im_ne_zero (z := 1 - z) (by simpa using hz)
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have he := (eq_div_iff hs).mp (Complex.Gamma_mul_Gamma_one_sub z)
  rw [mul_comm (Real.pi : ℂ) z] at he
  field_simp
  linear_combination -he

lemma sin_pi_nat_sub (a : ℕ) (z : ℂ) :
    Complex.sin ((Real.pi : ℂ) * ((a : ℂ) - z)) =
      (-1 : ℂ) ^ (a + 1) * Complex.sin ((Real.pi : ℂ) * z) := by
  have hc : Complex.cos ((a : ℂ) * (Real.pi : ℂ)) = (-1 : ℂ) ^ a := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_cos,
      Real.cos_nat_mul_pi]
    push_cast
    rfl
  rw [show (Real.pi : ℂ) * ((a : ℂ) - z) =
    (a : ℂ) * (Real.pi : ℂ) - (Real.pi : ℂ) * z by ring,
    Complex.sin_sub, Complex.sin_nat_mul_pi, hc, pow_succ]
  ring

lemma neg_one_pow_succ_div (a b : ℕ) :
    (-1 : ℂ) ^ (a + 1) / (-1 : ℂ) ^ (b + 1) = (-1 : ℂ) ^ (a + b) := by
  simp [div_eq_mul_inv, pow_add, pow_succ, ← inv_pow]

lemma gamma_integer_ratio_reflect (H h : ℕ) (hh : h ≤ H + 1)
    (z : ℂ) (hz : z.im ≠ 0) :
    Complex.Gamma ((h : ℂ) - z) / Complex.Gamma (1 + (H : ℂ) - h - z) =
      (-1 : ℂ) ^ (H + 1) *
        (Complex.Gamma ((h : ℂ) + z - H) / Complex.Gamma (1 - (h : ℂ) + z)) := by
  have hi1 : ((h : ℂ) - z).im ≠ 0 := by simpa using hz
  have hi2 : (1 + (H : ℂ) - h - z).im ≠ 0 := by simpa using hz
  have he : 1 + (H : ℂ) - h = (H + 1 - h : ℕ) := by
    rw [Nat.cast_sub hh]
    push_cast
    ring
  have hratio : Complex.sin ((Real.pi : ℂ) * (1 + (H : ℂ) - h - z)) /
      Complex.sin ((Real.pi : ℂ) * ((h : ℂ) - z)) = (-1 : ℂ) ^ (H + 1) := by
    rw [he, sin_pi_nat_sub, sin_pi_nat_sub, mul_div_mul_right _ _
      (sin_pi_mul_ne_zero_of_im hz), neg_one_pow_succ_div]
    congr 1
    omega
  rw [gamma_ratio_reflect hi1 hi2, hratio]
  congr 2 <;> congr 1 <;> ring

end ZudilinZeta
end
end


-- Source module: missions.zudilin.GammaModelReflection
section
set_option autoImplicit false
noncomputable section
open Complex Polynomial Finset
namespace ZudilinZeta

def complexGammaConstant (P : Params) (n : ℕ) : ℂ :=
  (∏ j ∈ Icc 1 P.r, (1 / ((hh P n j - 1).factorial : ℂ))) ^ 2 *
    ∏ j ∈ Icc (P.r + 1) P.q, ((hh P n 0 - 2 * hh P n j).factorial : ℂ)

def complexReflectedGammaKernel (P : Params) (n : ℕ) (z : ℂ) : ℂ :=
  ((hh P n 0 : ℂ) - 2 * z) *
    (Complex.Gamma z * Complex.Gamma ((hh P n 0 : ℂ) - z)) ^ P.r *
    (∏ j ∈ Icc 1 P.q,
      Complex.Gamma ((hh P n j : ℂ) + z - hh P n 0) /
        Complex.Gamma (1 - (hh P n j : ℂ) + z)) * complexGammaConstant P n

lemma complexGammaR_factored (P : Params) (n : ℕ) (z : ℂ) :
    complexGammaR P n z = ((hh P n 0 : ℂ) + 2 * z) *
      (Complex.Gamma ((hh P n 0 : ℂ) + z) / Complex.Gamma (1 + z)) ^ P.r *
      (∏ j ∈ Icc 1 P.q, Complex.Gamma ((hh P n j : ℂ) + z) /
        Complex.Gamma (1 + (hh P n 0 : ℂ) - hh P n j + z)) * complexGammaConstant P n := by
  have hqr := P.q_ge
  have hu : Icc 1 P.q = Icc 1 P.r ∪ Icc (P.r + 1) P.q := by
    ext j
    simp only [mem_Icc, mem_union]
    omega
  have hd : Disjoint (Icc 1 P.r) (Icc (P.r + 1) P.q) := by
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    have := mem_Icc.mp hj
    have := mem_Icc.mp hj'
    omega
  rw [hu, prod_union hd]
  simp only [complexGammaR, complexGammaConstant, prod_div_distrib,
    prod_mul_distrib, prod_const, Nat.card_Icc, Nat.add_sub_cancel, div_pow,
    div_eq_mul_inv, mul_inv_rev]
  ring

lemma complexGammaR_reflection (P : Params) (n : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    complexGammaR P n (-z) = (-1 : ℂ) ^ ((hh P n 0 + 1) * P.q) *
      (Complex.sin ((Real.pi : ℂ) * z) / (Real.pi : ℂ)) ^ P.r *
        complexReflectedGammaKernel P n z := by
  have hp (j : ℕ) (hj : j ∈ Icc 1 P.q) :
      Complex.Gamma ((hh P n j : ℂ) - z) /
        Complex.Gamma (1 + (hh P n 0 : ℂ) - hh P n j - z) =
      (-1 : ℂ) ^ (hh P n 0 + 1) *
        (Complex.Gamma ((hh P n j : ℂ) + z - hh P n 0) /
          Complex.Gamma (1 - (hh P n j : ℂ) + z)) := by
    apply gamma_integer_ratio_reflect
    · have := pf_hh_bounds P n j hj
      omega
    · exact hz
  have hmain : Complex.Gamma ((hh P n 0 : ℂ) - z) / Complex.Gamma (1 - z) =
      (Complex.Gamma z * Complex.Gamma ((hh P n 0 : ℂ) - z)) *
        (Complex.sin ((Real.pi : ℂ) * z) / (Real.pi : ℂ)) := by
    rw [div_eq_mul_inv, inv_gamma_one_sub hz]
    ring
  rw [complexGammaR_factored]
  simp only [mul_neg, ← sub_eq_add_neg]
  rw [hmain, prod_congr rfl hp, prod_mul_distrib, prod_const,
    Nat.card_Icc, Nat.add_sub_cancel, ← pow_mul]
  simp only [complexReflectedGammaKernel, mul_pow]
  ring

lemma complexRationalR_reflection_kernel (P : Params) (n : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    complexRationalR P n (-z) = (-1 : ℂ) ^ (hh P n 0 + 1) *
      (Complex.sin ((Real.pi : ℂ) * z) / (Real.pi : ℂ)) ^ P.r *
        complexReflectedGammaKernel P n z := by
  rw [complexRationalR, ← complexGammaR_expansion P n (-z) (by simpa using hz),
    complexGammaR_reflection P n z hz]
  rw [Nat.mul_comm (hh P n 0 + 1) P.q, pow_mul, P.q_odd.neg_one_pow]

end ZudilinZeta
end
end


-- Source module: missions.zudilin.Params13GammaKernelBridge
section
set_option autoImplicit false
noncomputable section
open Complex Polynomial Finset
namespace ZudilinZeta

lemma params13GammaConstant_explicit (n : ℕ) :
    complexGammaConstant params13 n = (1 / ((27 * n).factorial : ℂ)) ^ 6 *
      ∏ j ∈ Icc 4 13, (((91 - 2 * eta13 j) * n).factorial : ℂ) := by
  have hhead (j : ℕ) (hj : j ∈ Icc 1 3) : hh params13 n j - 1 = 27 * n := by
    obtain ⟨hlo, hhi⟩ := mem_Icc.mp hj
    interval_cases j <;> simp [hh, params13, eta13]
  have htail (j : ℕ) (hj : j ∈ Icc 4 13) :
      hh params13 n 0 - 2 * hh params13 n j = (91 - 2 * eta13 j) * n := by
    obtain ⟨hlo, hhi⟩ := mem_Icc.mp hj
    interval_cases j <;> norm_num [hh, params13, eta13] <;> omega
  unfold complexGammaConstant
  change (∏ j ∈ Icc 1 3, (1 / ((hh params13 n j - 1).factorial : ℂ))) ^ 2 *
    (∏ j ∈ Icc 4 13, ((hh params13 n 0 - 2 * hh params13 n j).factorial : ℂ)) = _
  have hp : (∏ j ∈ Icc 1 3, (1 / ((hh params13 n j - 1).factorial : ℂ))) =
      (1 / ((27 * n).factorial : ℂ)) ^ 3 := by
    calc
      _ = ∏ _j ∈ Icc 1 3, (1 / ((27 * n).factorial : ℂ)) :=
        prod_congr rfl (fun j hj => by rw [hhead j hj])
      _ = _ := by norm_num
  have hq : (∏ j ∈ Icc 4 13, ((hh params13 n 0 - 2 * hh params13 n j).factorial : ℂ)) =
      ∏ j ∈ Icc 4 13, (((91 - 2 * eta13 j) * n).factorial : ℂ) :=
    prod_congr rfl (fun j hj => by rw [htail j hj])
  rw [hp, hq]
  norm_num [← pow_mul]

lemma gamma_nat_mul_add_one (n k : ℕ) :
    Complex.Gamma ((n : ℂ) * k + 1) = ((k * n).factorial : ℂ) := by
  convert Complex.Gamma_nat_eq_factorial (k * n) using 1 <;> congr 1 <;> push_cast <;> ring

lemma params13_reflected_kernel_eq (n : ℕ) (z : ℂ) :
    complexReflectedGammaKernel params13 n ((n : ℂ) * z) = params13GammaKernel n z := by
  rw [complexReflectedGammaKernel, params13GammaConstant_explicit]
  norm_num [params13GammaKernel, params13GammaShiftIndex, params13GammaWeight,
    params13GammaBase, params13GammaSlope, params13GammaOffset, params13, hh, eta13,
    Finset.prod_range_succ, Finset.prod_Icc_succ_top]
  ring_nf
  have hΓ (k : ℕ) : Complex.Gamma (1 + (n : ℂ) * k) = ((k * n).factorial : ℂ) := by
    rw [add_comm]
    exact gamma_nat_mul_add_one n k
  have h27 : Complex.Gamma (1 + (n : ℂ) * 27) = ((n * 27).factorial : ℂ) := by
    simpa only [Nat.cast_ofNat, Nat.mul_comm] using hΓ 27
  have h33 : Complex.Gamma (1 + (n : ℂ) * 33) = ((n * 33).factorial : ℂ) := by
    simpa only [Nat.cast_ofNat, Nat.mul_comm] using hΓ 33
  have h31 : Complex.Gamma (1 + (n : ℂ) * 31) = ((n * 31).factorial : ℂ) := by
    simpa only [Nat.cast_ofNat, Nat.mul_comm] using hΓ 31
  have h29 : Complex.Gamma (1 + (n : ℂ) * 29) = ((n * 29).factorial : ℂ) := by
    simpa only [Nat.cast_ofNat, Nat.mul_comm] using hΓ 29
  have h25 : Complex.Gamma (1 + (n : ℂ) * 25) = ((n * 25).factorial : ℂ) := by
    simpa only [Nat.cast_ofNat, Nat.mul_comm] using hΓ 25
  have h23 : Complex.Gamma (1 + (n : ℂ) * 23) = ((n * 23).factorial : ℂ) := by
    simpa only [Nat.cast_ofNat, Nat.mul_comm] using hΓ 23
  have h21 : Complex.Gamma (1 + (n : ℂ) * 21) = ((n * 21).factorial : ℂ) := by
    simpa only [Nat.cast_ofNat, Nat.mul_comm] using hΓ 21
  have h19 : Complex.Gamma (1 + (n : ℂ) * 19) = ((n * 19).factorial : ℂ) := by
    simpa only [Nat.cast_ofNat, Nat.mul_comm] using hΓ 19
  have h17 : Complex.Gamma (1 + (n : ℂ) * 17) = ((n * 17).factorial : ℂ) := by
    simpa only [Nat.cast_ofNat, Nat.mul_comm] using hΓ 17
  have h15 : Complex.Gamma (1 + (n : ℂ) * 15) = ((n * 15).factorial : ℂ) := by
    simpa only [Nat.cast_ofNat, Nat.mul_comm] using hΓ 15
  simp only [h27, h33, h31, h29, h25, h23, h21, h19, h17, h15]

lemma params13_reflection_kernel (n : ℕ) (z : ℂ) (hz : ((n : ℂ) * z).im ≠ 0) :
    complexRationalR params13 n (-((n : ℂ) * z)) = (-1 : ℂ) ^ (n + 1) *
      (Complex.sin ((Real.pi : ℂ) * ((n : ℂ) * z)) / (Real.pi : ℂ)) ^ 3 *
        params13GammaKernel n z := by
  rw [complexRationalR_reflection_kernel params13 n ((n : ℂ) * z) hz,
    params13_reflected_kernel_eq]
  norm_num [hh, params13, eta13, pow_add, pow_mul]

lemma params13_cubic_sine_kernel (n : ℕ) (z : ℂ)
    (hz : ((n : ℂ) * z).im ≠ 0) :
    complexRationalR params13 n (-((n : ℂ) * z)) *
        ((Real.pi : ℂ) ^ 3 * Complex.cos ((Real.pi : ℂ) * ((n : ℂ) * z)) /
          Complex.sin ((Real.pi : ℂ) * ((n : ℂ) * z)) ^ 3) =
      (-1 : ℂ) ^ (n + 1) * params13GammaKernel n z *
        Complex.cos ((Real.pi : ℂ) * ((n : ℂ) * z)) := by
  rw [params13_reflection_kernel n z hz]
  have hs := sin_pi_mul_ne_zero_of_im hz
  have hs' : Complex.sin ((Real.pi : ℂ) * (n : ℂ) * z) ≠ 0 := by
    simpa only [mul_assoc] using hs
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hs', hp] <;> ring

end ZudilinZeta
end
end


-- Source module: missions.zudilin.ComplexPartialFractions
section
set_option autoImplicit false

open Polynomial Finset

/-- A simultaneous complex evaluation of Mathlib's partial fractions, with rational residues. -/
lemma complex_rational_partial_fraction_variable_expansion (K : Finset ℕ) (μ : ℕ → ℕ) (A : ℚ[X]) :
    ∃ (Q : ℚ[X]) (c : (k : ℕ) → Fin (μ k) → ℚ),
      ∀ t : ℂ, (∀ k ∈ K, t + (k : ℂ) ≠ 0) →
        A.eval₂ (algebraMap ℚ ℂ) t / (∏ k ∈ K, (t + (k : ℂ)) ^ (μ k)) =
          Q.eval₂ (algebraMap ℚ ℂ) t +
            ∑ k ∈ K, ∑ j : Fin (μ k), (c k j : ℂ) / (t + (k : ℂ)) ^ (j.val + 1) := by
  classical
  let U := {t : ℂ // ∀ k ∈ K, t + (k : ℂ) ≠ 0}
  let ev : ℚ[X] →+* (U → ℂ) :=
    RingHom.pi (fun t => Polynomial.eval₂RingHom (algebraMap ℚ ℂ) t.val)
  let : Algebra ℚ[X] (U → ℂ) := ev.toAlgebra
  let g : ℕ → ℚ[X] := fun k => X + C (k : ℚ)
  have hg (k : ℕ) (hk : k ∈ K) : (g k).Monic := monic_X_add_C _
  have hcop : Set.Pairwise (↑K : Set ℕ) (fun k l => IsCoprime (g k) (g l)) := by
    intro k hk l hl hkl
    have h : Function.Injective (fun k : ℕ => -(k : ℚ)) := by
      intro a b hab
      exact_mod_cast neg_injective hab
    simpa only [g, map_neg, sub_neg_eq_add] using pairwise_coprime_X_sub_C h hkl
  let gi : ℕ → U → ℂ := fun k t => (t.val + (k : ℂ))⁻¹
  have hgi (k : ℕ) (hk : k ∈ K) : gi k * algebraMap ℚ[X] (U → ℂ) (g k) = 1 := by
    funext t
    change (t.val + (k : ℂ))⁻¹ * (g k).eval₂ (algebraMap ℚ ℂ) t.val = 1
    simpa [g] using inv_mul_cancel₀ (t.property k hk)
  obtain ⟨Q, c, hc, he⟩ :=
    mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse A hg hcop μ hgi
  refine ⟨Q, fun k j => (c k j).coeff 0, ?_⟩
  intro t ht
  have he' := congrFun he (⟨t, ht⟩ : U)
  simp only [Pi.mul_apply, Pi.add_apply, Finset.prod_apply, Finset.sum_apply,
    Pi.pow_apply] at he'
  change A.eval₂ (algebraMap ℚ ℂ) t * (∏ k ∈ K, ((t + (k : ℂ))⁻¹)^(μ k)) =
    Q.eval₂ (algebraMap ℚ ℂ) t +
      ∑ k ∈ K, ∑ j : Fin (μ k), (c k j).eval₂ (algebraMap ℚ ℂ) t *
        ((t + (k : ℂ))⁻¹)^(j.val+1) at he'
  have hconst (k : ℕ) (hk : k ∈ K) (j : Fin (μ k)) :
      (c k j).eval₂ (algebraMap ℚ ℂ) t = ((c k j).coeff 0 : ℂ) := by
    have hd := hc k hk j
    simp only [g, degree_X_add_C] at hd
    have hd' : (c k j).degree ≤ 0 := by exact (Order.lt_succ_iff).mp hd
    conv_lhs => rw [eq_C_of_degree_le_zero hd', eval₂_C]
    rfl
  simp only [inv_pow, prod_inv_distrib, ← div_eq_mul_inv] at he'
  rw [he']
  congr 1
  apply sum_congr rfl
  intro k hk
  apply sum_congr rfl
  intro j hj
  rw [hconst k hk j]


open Filter
open scoped Topology

/-- Decay at infinity eliminates the polynomial part of a rational partial fraction expansion. -/
lemma proper_complex_rational_partial_fraction_variable_expansion (K : Finset ℕ) (μ : ℕ → ℕ) (A : ℚ[X])
    (hlim : Tendsto (fun t : ℝ => A.eval₂ (algebraMap ℚ ℝ) t /
      (∏ k ∈ K, (t + (k : ℝ)) ^ (μ k))) atTop (𝓝 0)) :
    ∃ c : (k : ℕ) → Fin (μ k) → ℚ,
      ∀ t : ℂ, (∀ k ∈ K, t + (k : ℂ) ≠ 0) →
        A.eval₂ (algebraMap ℚ ℂ) t / (∏ k ∈ K, (t + (k : ℂ)) ^ (μ k)) =
          ∑ k ∈ K, ∑ j : Fin (μ k), (c k j : ℂ) / (t + (k : ℂ)) ^ (j.val + 1) := by
  obtain ⟨Q, c, he⟩ := complex_rational_partial_fraction_variable_expansion K μ A
  have her (t : ℝ) (ht : ∀ k ∈ K, t + (k : ℝ) ≠ 0) :
      A.eval₂ (algebraMap ℚ ℝ) t / (∏ k ∈ K, (t + (k : ℝ)) ^ (μ k)) =
        Q.eval₂ (algebraMap ℚ ℝ) t +
          ∑ k ∈ K, ∑ j : Fin (μ k), (c k j : ℝ) / (t + (k : ℝ)) ^ (j.val + 1) := by
    have h := he (t : ℂ) (fun k hk => by exact_mod_cast ht k hk)
    apply Complex.ofReal_injective
    push_cast
    simpa only [ZudilinZeta.polynomial_eval₂_complex_ofReal] using h
  have hc : Tendsto (fun t : ℝ => ∑ k ∈ K, ∑ j : Fin (μ k),
      (c k j : ℝ) / (t + (k : ℝ)) ^ (j.val+1)) atTop (𝓝 0) := by
    have h (k : ℕ) (j : Fin (μ k)) : Tendsto
        (fun t : ℝ => (c k j : ℝ) / (t + (k : ℝ)) ^ (j.val+1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by omega : j.val+1 ≠ 0)).comp
        (tendsto_id.atTop_add tendsto_const_nhds))
    simpa only [sum_const_zero] using tendsto_finsetSum K (fun k hk =>
      tendsto_finsetSum univ (fun j hj => h k j))
  have hq : Tendsto (fun t : ℝ => Q.eval₂ (algebraMap ℚ ℝ) t) atTop (𝓝 0) := by
    have h := hlim.sub hc
    simp only [sub_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [her t (fun k hk => (add_pos_of_pos_of_nonneg ht (Nat.cast_nonneg k)).ne')]
    simp
  have hq0 : Q.map (algebraMap ℚ ℝ) = 0 := by
    apply leadingCoeff_eq_zero.mp
    apply ((Q.map (algebraMap ℚ ℝ)).tendsto_nhds_iff.mp ?_).1
    simpa only [eval_map] using hq
  refine ⟨c, fun t ht => ?_⟩
  have hQ : Q = 0 := by
    exact Polynomial.map_injective (algebraMap ℚ ℝ) (Rat.cast_injective (α := ℝ)) (by simpa using hq0)
  have hQeval : Q.eval₂ (algebraMap ℚ ℂ) t = 0 := by simp [hQ]
  simpa only [hQeval, zero_add] using he t ht
end


-- Source module: missions.zudilin.ComplexRationalBounds
section
set_option autoImplicit false
noncomputable section
open Complex Polynomial Finset Filter Topology

namespace ZudilinZeta

lemma complex_pf_uniform_model (P : Params) (n : ℕ) :
    ∃ A : ℚ[X], ∀ t : ℂ, (∀ k ∈ poleRange P n, t+(k : ℂ) ≠ 0) →
      A.eval₂ (algebraMap ℚ ℂ) t / (∏ k ∈ poleRange P n, (t+(k : ℂ))^(P.q-P.r)) =
        (pfNumerator P n).eval₂ (algebraMap ℚ ℂ) t /
          (pfDenominator P n).eval₂ (algebraMap ℚ ℂ) t := by
  obtain ⟨B, hB⟩ := pfDenominator_dvd_uniform P n
  refine ⟨pfNumerator P n * B, ?_⟩
  intro t ht
  have hn : (∏ k ∈ poleRange P n, (t+(k : ℂ))^(P.q-P.r)) ≠ 0 :=
    prod_ne_zero_iff.mpr (fun k hk => pow_ne_zero _ (ht k hk))
  have he := congrArg (fun p : ℚ[X] => p.eval₂ (algebraMap ℚ ℂ) t) hB
  simp only [eval₂_finsetProd, eval₂_pow, eval₂_mul, eval₂_add, eval₂_X, eval₂_C,
    map_natCast, eval₂_natCast] at he
  have hB0 : B.eval₂ (algebraMap ℚ ℂ) t ≠ 0 := by
    intro hz
    apply hn
    rw [he, hz, mul_zero]
  rw [eval₂_mul, he, mul_div_mul_right _ _ hB0]


lemma complexRationalR_partial_fractions (P : Params) (n : ℕ) :
    ∃ c : (k : ℕ) → Fin (P.q - P.r) → ℚ,
      ∀ z : ℂ, (∀ k ∈ poleRange P n, z + (k : ℂ) ≠ 0) →
        complexRationalR P n z =
          ∑ k ∈ poleRange P n, ∑ j : Fin (P.q - P.r),
            (c k j : ℂ) / (z + (k : ℂ)) ^ (j.val + 1) := by
  obtain ⟨A, hA⟩ := complex_pf_uniform_model P n
  have hlim : Tendsto (fun t : ℝ => A.eval₂ (algebraMap ℚ ℝ) t /
      (∏ k ∈ poleRange P n, (t + (k : ℝ)) ^ (P.q - P.r))) atTop (𝓝 0) := by
    apply (rational_function_decay P n).1.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hpoles (k : ℕ) (_hk : k ∈ poleRange P n) : (t : ℂ) + (k : ℂ) ≠ 0 := by
      exact_mod_cast (add_pos_of_pos_of_nonneg ht (Nat.cast_nonneg k)).ne'
    have he := hA (t : ℂ) hpoles
    change _ = complexRationalR P n (t : ℂ) at he
    rw [complexRationalR_ofReal P n t (by linarith)] at he
    apply Complex.ofReal_injective
    push_cast
    simpa only [polynomial_eval₂_complex_ofReal] using he.symm
  obtain ⟨c, hc⟩ := proper_complex_rational_partial_fraction_variable_expansion
    (poleRange P n) (fun _ => P.q - P.r) A hlim
  refine ⟨c, fun z hz => ?_⟩
  rw [← hc z hz, hA z hz]
  rfl

lemma complexRationalR_uniform_bound (P : Params) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ) (z : ℂ), 1 ≤ B →
      (∀ k ∈ poleRange P n, B ≤ ‖z + (k : ℂ)‖) →
        ‖complexRationalR P n z‖ ≤ C / B := by
  obtain ⟨c, hc⟩ := complexRationalR_partial_fractions P n
  let C : ℝ := ∑ k ∈ poleRange P n, ∑ j : Fin (P.q - P.r), ‖(c k j : ℂ)‖
  refine ⟨C, sum_nonneg (fun k hk => sum_nonneg (fun j hj => norm_nonneg _)), ?_⟩
  intro B z hB hz
  have hBp : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hnz (k : ℕ) (hk : k ∈ poleRange P n) : z + (k : ℂ) ≠ 0 :=
    norm_pos_iff.mp (hBp.trans_le (hz k hk))
  rw [hc z hnz]
  calc
    _ ≤ ∑ k ∈ poleRange P n, ∑ j : Fin (P.q - P.r),
        ‖(c k j : ℂ) / (z + (k : ℂ)) ^ (j.val + 1)‖ :=
      (norm_sum_le _ _).trans (sum_le_sum (fun k hk => norm_sum_le _ _))
    _ ≤ ∑ k ∈ poleRange P n, ∑ j : Fin (P.q - P.r), ‖(c k j : ℂ)‖ / B := by
      apply sum_le_sum
      intro k hk
      apply sum_le_sum
      intro j hj
      rw [norm_div, norm_pow]
      apply div_le_div_of_nonneg_left (norm_nonneg _) hBp
      exact (hz k hk).trans (le_self_pow₀ (hB.trans (hz k hk)) (by omega))
    _ = C / B := by simp only [C, Finset.sum_div]

end ZudilinZeta
end
end


-- Source module: missions.zudilin.Params13RationalBounds
section
set_option autoImplicit false
noncomputable section
open Complex Polynomial Finset Filter Topology

namespace ZudilinZeta

lemma params13_pole_le (n k : ℕ) (hk : k ∈ poleRange params13 n) : k ≤ 62 * n + 1 := by
  norm_num [poleRange, hh, params13, eta13] at hk
  omega

lemma pfDenominator_ne_zero_of_poleRange (P : Params) (n : ℕ) (z : ℂ)
    (hz : ∀ k ∈ poleRange P n, z + (k : ℂ) ≠ 0) :
    (pfDenominator P n).eval₂ (algebraMap ℚ ℂ) z ≠ 0 := by
  obtain ⟨B, hB⟩ := pfDenominator_dvd_uniform P n
  have hn : (∏ k ∈ poleRange P n, (z + (k : ℂ)) ^ (P.q - P.r)) ≠ 0 :=
    prod_ne_zero_iff.mpr (fun k hk => pow_ne_zero _ (hz k hk))
  have he := congrArg (fun p : ℚ[X] => p.eval₂ (algebraMap ℚ ℂ) z) hB
  simp only [eval₂_finsetProd, eval₂_pow, eval₂_mul, eval₂_add, eval₂_X,
    map_natCast, eval₂_natCast] at he
  intro h
  exact hn (by rw [he, h, zero_mul])

lemma params13_poles_away (n : ℕ) (s : ℂ) (hs : 62 * (n : ℝ) + 1 < s.re) :
    ∀ k ∈ poleRange params13 n, -s + (k : ℂ) ≠ 0 := by
  intro k hk he
  have hk' : (k : ℝ) ≤ 62 * n + 1 := by exact_mod_cast params13_pole_le n k hk
  have h := congrArg Complex.re he
  simp only [add_re, neg_re, natCast_re, zero_re] at h
  linarith

lemma analyticAt_params13_neg_rational (n : ℕ) (s : ℂ)
    (hs : 62 * (n : ℝ) + 1 < s.re) :
    AnalyticAt ℂ (fun z => complexRationalR params13 n (-z)) s := by
  exact (analyticAt_complexRationalR params13 n (-s)
    (pfDenominator_ne_zero_of_poleRange params13 n (-s) (params13_poles_away n s hs))).comp
      analyticAt_id.neg

lemma params13_rational_bounds (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    (∀ s : ℂ, 62 * (n : ℝ) + 2 ≤ s.re →
      ‖complexRationalR params13 n (-s)‖ ≤ C / (s.re - (62 * n + 1))) ∧
    (∀ s : ℂ, 1 ≤ |s.im| → ‖complexRationalR params13 n (-s)‖ ≤ C / |s.im|) := by
  obtain ⟨C, hC, hc⟩ := complexRationalR_uniform_bound params13 n
  refine ⟨C, hC, ?_, ?_⟩
  · intro s hs
    apply hc _ _ (by linarith)
    intro k hk
    have hk' : (k : ℝ) ≤ 62 * n + 1 := by exact_mod_cast params13_pole_le n k hk
    have hnorm := Complex.abs_re_le_norm (-s + (k : ℂ))
    simp only [add_re, neg_re, natCast_re] at hnorm
    rw [abs_of_nonpos (by linarith : -s.re + (k : ℝ) ≤ 0)] at hnorm
    linarith
  · intro s hs
    apply hc _ _ hs
    intro k hk
    simpa only [add_im, neg_im, natCast_im, add_zero, abs_neg] using
      Complex.abs_im_le_norm (-s + (k : ℂ))

end ZudilinZeta
end
end


-- Source module: missions.zudilin.CotangentRectangle
section
set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology

namespace ZudilinZeta

lemma analyticAt_sin_pi_mul (z : ℂ) :
    AnalyticAt ℂ (fun s : ℂ => Complex.sin (Real.pi * s)) z :=
  Complex.analyticAt_sin.comp (analyticAt_const.mul analyticAt_id)

lemma sin_pi_mul_eq_zero_iff_integer (z : ℂ) :
    Complex.sin (Real.pi * z) = 0 ↔ ∃ k : ℤ, z = (k : ℂ) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [Complex.sin_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    apply mul_left_cancel₀ hpi
    simpa only [mul_comm] using hk
  · rintro ⟨k, rfl⟩
    exact ⟨k, mul_comm _ _⟩

lemma sin_pi_mul_analyticOrderNatAt {z : ℂ}
    (hz : Complex.sin (Real.pi * z) = 0) :
    analyticOrderNatAt (fun s : ℂ => Complex.sin (Real.pi * s)) z = 1 := by
  have hcos : Complex.cos (Real.pi * z) ≠ 0 := by
    intro h
    have := Complex.sin_sq_add_cos_sq (Real.pi * z)
    simp only [hz, h, zero_pow (by decide : 2 ≠ 0), zero_add] at this
    exact zero_ne_one this
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hd : HasDerivAt (fun s : ℂ => Complex.sin (Real.pi * s))
      (Complex.cos (Real.pi * z) * Real.pi) z := by
    convert! (Complex.hasDerivAt_sin (Real.pi * z)).comp z
      ((hasDerivAt_id z).const_mul (Real.pi : ℂ)) using 1 <;> simp
  have ho := (analyticAt_sin_pi_mul z).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz
    (by rw [hd.deriv]; exact mul_ne_zero hcos hpi)
  simpa [analyticOrderNatAt, ho]

lemma logDeriv_sin_pi_mul (z : ℂ) :
    logDeriv (fun s : ℂ => Complex.sin (Real.pi * s)) z =
      Real.pi * Complex.cot (Real.pi * z) := by
  have hd : HasDerivAt (fun s : ℂ => Complex.sin (Real.pi * s))
      (Complex.cos (Real.pi * z) * Real.pi) z := by
    convert! (Complex.hasDerivAt_sin (Real.pi * z)).comp z
      ((hasDerivAt_id z).const_mul (Real.pi : ℂ)) using 1 <;> simp
  rw [logDeriv_apply, hd.deriv, Complex.cot]
  ring

lemma rectangleIntegralPrime_pi_cot {g : ℂ → ℂ} {z w : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im) (Z : Finset ℂ)
    (hg : AnalyticOnNhd ℂ g (Rectangle z w))
    (hborder : ∀ s ∈ RectangleBorder z w, Complex.sin (Real.pi * s) ≠ 0)
    (hZ : ∀ s ∈ Rectangle z w, Complex.sin (Real.pi * s) = 0 ↔ s ∈ Z)
    (hZsub : (Z : Set ℂ) ⊆ Rectangle z w) :
    RectangleIntegral' (fun s => g s * (Real.pi * Complex.cot (Real.pi * s))) z w =
      ∑ ρ ∈ Z, g ρ := by
  have h := Zeta23.Analytic.rectangleIntegralPrime_mul_logDeriv_of_poles
    (f := fun s : ℂ => Complex.sin (Real.pi * s)) (g := g) hre him Z ∅
    (Finset.disjoint_empty_right Z) (by simp)
    (fun s _ => analyticAt_sin_pi_mul s) hg hborder
    (by simpa using hZ) hZsub (fun _ => 0) (by simp)
  simp only [Finset.sum_empty, sub_zero, logDeriv_sin_pi_mul] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [sin_pi_mul_analyticOrderNatAt ((hZ ρ (hZsub hρ)).mpr hρ), Nat.cast_one, one_mul]

end ZudilinZeta
end
end


-- Source module: missions.zudilin.CotangentDerivatives
section
set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology

namespace ZudilinZeta

def piCot (s : ℂ) : ℂ := Real.pi * Complex.cot (Real.pi * s)
def piCotD (s : ℂ) : ℂ := -(Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * s) ^ 2
def cubicCotKernel (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ 3 * Complex.cos (Real.pi * s) / Complex.sin (Real.pi * s) ^ 3

lemma hasDerivAt_sin_pi_mul (s : ℂ) :
    HasDerivAt (fun z : ℂ => Complex.sin (Real.pi * z))
      (Complex.cos (Real.pi * s) * Real.pi) s := by
  convert! (Complex.hasDerivAt_sin (Real.pi * s)).comp s
    ((hasDerivAt_id s).const_mul (Real.pi : ℂ)) using 1 <;> simp

lemma hasDerivAt_cos_pi_mul (s : ℂ) :
    HasDerivAt (fun z : ℂ => Complex.cos (Real.pi * z))
      (-Complex.sin (Real.pi * s) * Real.pi) s := by
  convert! (Complex.hasDerivAt_cos (Real.pi * s)).comp s
    ((hasDerivAt_id s).const_mul (Real.pi : ℂ)) using 1 <;> simp

lemma hasDerivAt_piCot (s : ℂ) (hs : Complex.sin (Real.pi * s) ≠ 0) :
    HasDerivAt piCot (piCotD s) s := by
  have h := ((hasDerivAt_cos_pi_mul s).div (hasDerivAt_sin_pi_mul s) hs).const_mul
    (Real.pi : ℂ)
  convert! h using 1
  dsimp only [piCotD]
  field_simp
  linear_combination Complex.sin_sq_add_cos_sq (Real.pi * s)

lemma hasDerivAt_piCotD (s : ℂ) (hs : Complex.sin (Real.pi * s) ≠ 0) :
    HasDerivAt piCotD (2 * cubicCotKernel s) s := by
  have h := (hasDerivAt_const s (-(Real.pi : ℂ) ^ 2)).div
    ((hasDerivAt_sin_pi_mul s).fun_pow 2) (pow_ne_zero _ hs)
  convert! h using 1
  dsimp only [cubicCotKernel]
  field_simp
  ring

lemma analyticAt_piCot (s : ℂ) (hs : Complex.sin (Real.pi * s) ≠ 0) :
    AnalyticAt ℂ piCot s := by
  exact analyticAt_const.mul
    ((Complex.analyticAt_cos.comp (analyticAt_const.mul analyticAt_id)).div
      (analyticAt_sin_pi_mul s) hs)

lemma analyticAt_cubicCotKernel (s : ℂ) (hs : Complex.sin (Real.pi * s) ≠ 0) :
    AnalyticAt ℂ cubicCotKernel s := by
  exact (analyticAt_const.mul
    (Complex.analyticAt_cos.comp (analyticAt_const.mul analyticAt_id))).div
      ((analyticAt_sin_pi_mul s).pow 3) (pow_ne_zero _ hs)

end ZudilinZeta
end
end


-- Source module: missions.zudilin.CubicCotangentBounds
section
set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology

namespace ZudilinZeta

lemma norm_sin_sq (z : ℂ) :
    ‖Complex.sin z‖ ^ 2 = Real.sin z.re ^ 2 + Real.sinh z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.sin_eq]
  simp only [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sinh,
    ← Complex.ofReal_cosh, ← Complex.ofReal_mul, Complex.normSq_apply,
    add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul,
    sub_zero, add_zero, add_im, mul_im, mul_one, zero_add]
  nlinarith [Real.sin_sq_add_cos_sq z.re, Real.cosh_sq_sub_sinh_sq z.im]

lemma norm_cos_sq (z : ℂ) :
    ‖Complex.cos z‖ ^ 2 = Real.cos z.re ^ 2 + Real.sinh z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.cos_eq]
  simp only [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sinh,
    ← Complex.ofReal_cosh, ← Complex.ofReal_mul, Complex.normSq_apply,
    sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul,
    sub_zero, sub_im, mul_im, mul_one, zero_add, zero_sub]
  nlinarith [Real.sin_sq_add_cos_sq z.re, Real.cosh_sq_sub_sinh_sq z.im]

lemma norm_cos_le_exp_abs_im (z : ℂ) :
    ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  have hnorm : ‖Complex.cos z‖ ≤ Real.cosh z.im := by
    have h := norm_cos_sq z
    have hc := Real.cos_sq_le_one z.re
    have hhyp := Real.cosh_sq_sub_sinh_sq z.im
    have hp := Real.cosh_pos z.im
    nlinarith [norm_nonneg (Complex.cos z)]
  apply hnorm.trans
  rw [← Real.cosh_abs, Real.cosh_eq]
  have h := Real.exp_le_exp.mpr (show -|z.im| ≤ |z.im| by linarith [abs_nonneg z.im])
  linarith

lemma exp_abs_im_le_four_norm_sin (z : ℂ) (hz : 1 ≤ |z.im|) :
    Real.exp |z.im| ≤ 4 * ‖Complex.sin z‖ := by
  have hnorm : Real.sinh |z.im| ≤ ‖Complex.sin z‖ := by
    rw [← Real.abs_sinh]
    have h := norm_sin_sq z
    nlinarith [sq_nonneg (Real.sin z.re), norm_nonneg (Complex.sin z), sq_abs (Real.sinh z.im)]
  have he : 2 ≤ Real.exp |z.im| := by
    have h := Real.add_one_le_exp |z.im|
    linarith
  have hn : Real.exp (-|z.im|) ≤ 1 := by
    simpa using Real.exp_le_exp.mpr (show -|z.im| ≤ 0 by linarith [abs_nonneg z.im])
  have hsh := Real.sinh_eq |z.im|
  linarith

lemma exp_abs_im_le_two_norm_sin (z : ℂ) (hz : Real.sin z.re ^ 2 = 1) :
    Real.exp |z.im| ≤ 2 * ‖Complex.sin z‖ := by
  have hnorm : ‖Complex.sin z‖ = Real.cosh |z.im| := by
    have h := norm_sin_sq z
    rw [hz] at h
    rw [Real.cosh_abs]
    have hcosh := Real.cosh_sq_sub_sinh_sq z.im
    nlinarith [norm_nonneg (Complex.sin z), Real.cosh_pos z.im]
  rw [hnorm, Real.cosh_eq]
  linarith [Real.exp_pos (-|z.im|)]

lemma norm_cos_div_sin_cube_le (z : ℂ)
    (hz : Real.exp |z.im| ≤ 4 * ‖Complex.sin z‖) :
    ‖Complex.cos z / Complex.sin z ^ 3‖ ≤ 64 * Real.exp (-2 * |z.im|) := by
  have hp : 0 < Real.exp |z.im| / 4 := by positivity
  calc
    _ = ‖Complex.cos z‖ / ‖Complex.sin z‖ ^ 3 := by rw [norm_div, norm_pow]
    _ ≤ Real.exp |z.im| / (Real.exp |z.im| / 4) ^ 3 := by
      apply div_le_div₀ (by positivity) (norm_cos_le_exp_abs_im z) (pow_pos hp 3)
      gcongr
      linarith
    _ = 64 * Real.exp (-2 * |z.im|) := by
      rw [show -2 * |z.im| = -(|z.im| + |z.im|) by ring, Real.exp_neg, Real.exp_add]
      field_simp <;> norm_num

lemma norm_cubicCotKernel_bound (s : ℂ)
    (hs : Real.exp |((Real.pi : ℂ) * s).im| ≤
      4 * ‖Complex.sin ((Real.pi : ℂ) * s)‖) :
    ‖cubicCotKernel s‖ ≤ 64 * Real.pi ^ 3 * Real.exp (-2 * Real.pi * |s.im|) := by
  have h := norm_cos_div_sin_cube_le ((Real.pi : ℂ) * s) hs
  calc
    _ = Real.pi ^ 3 * ‖Complex.cos (Real.pi * s) / Complex.sin (Real.pi * s) ^ 3‖ := by
      rw [cubicCotKernel, mul_div_assoc, norm_mul, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    _ ≤ Real.pi ^ 3 * (64 * Real.exp (-2 * |((Real.pi : ℂ) * s).im|)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by
      simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero,
        abs_mul, abs_of_pos Real.pi_pos]
      ring

lemma norm_cubicCotKernel_horizontal (s : ℂ) (hs : 1 ≤ |s.im|) :
    ‖cubicCotKernel s‖ ≤ 64 * Real.pi ^ 3 * Real.exp (-2 * Real.pi * |s.im|) := by
  apply norm_cubicCotKernel_bound
  apply exp_abs_im_le_four_norm_sin
  simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero,
    abs_mul, abs_of_pos Real.pi_pos]
  nlinarith [Real.pi_gt_three]

lemma norm_cubicCotKernel_half_integer (k : ℤ) (y : ℝ) :
    ‖cubicCotKernel ((k : ℂ) + 1 / 2 + (y : ℂ) * I)‖ ≤
      64 * Real.pi ^ 3 * Real.exp (-2 * Real.pi * |y|) := by
  have hs : Real.sin (((Real.pi : ℂ) * ((k : ℂ) + 1 / 2 + (y : ℂ) * I)).re) ^ 2 = 1 := by
    have he : ((Real.pi : ℂ) * ((k : ℂ) + 1 / 2 + (y : ℂ) * I)).re =
        (k : ℝ) * Real.pi + Real.pi / 2 := by simp; ring
    rw [he, Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two,
      mul_zero, zero_add, mul_one]
    have h := Real.abs_cos_int_mul_pi k
    nlinarith [sq_abs (Real.cos ((k : ℝ) * Real.pi))]
  have h := exp_abs_im_le_two_norm_sin _ hs
  have hh := norm_cubicCotKernel_bound ((k : ℂ) + 1 / 2 + (y : ℂ) * I)
    (by linarith [norm_nonneg (Complex.sin ((Real.pi : ℂ) * ((k : ℂ) + 1 / 2 + (y : ℂ) * I)))])
  simpa using hh

end ZudilinZeta
end
end


-- Source module: missions.zudilin.CotangentIntegerResidues
section
set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology

namespace ZudilinZeta

def cotLowerCorner (a : ℤ) (T : ℝ) : ℂ := (a : ℂ) + 1 / 2 - (T : ℂ) * I
def cotUpperCorner (b : ℤ) (T : ℝ) : ℂ := (b : ℂ) + 1 / 2 + (T : ℂ) * I

lemma int_mem_half_interval (a b k : ℤ) :
    ((a : ℝ) + 1 / 2 ≤ k ∧ (k : ℝ) ≤ b + 1 / 2) ↔ a < k ∧ k ≤ b := by
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor
    · by_contra h
      have hk : (k : ℝ) ≤ a := by exact_mod_cast (le_of_not_gt h)
      linarith
    · by_contra h
      have hk : (b : ℝ) + 1 ≤ k := by exact_mod_cast (show b + 1 ≤ k by omega)
      linarith
  · rintro ⟨hlo, hhi⟩
    have hl : (a : ℝ) + 1 ≤ k := by exact_mod_cast (show a + 1 ≤ k by omega)
    have hh : (k : ℝ) ≤ b := by exact_mod_cast hhi
    constructor <;> linarith

lemma int_ne_half_integer (a k : ℤ) : (k : ℝ) ≠ a + 1 / 2 := by
  intro hk
  have h := (int_mem_half_interval a a k).mp ⟨hk.ge, hk.le⟩
  omega

lemma int_mem_cotRectangle (a b k : ℤ) (T : ℝ) (hab : a ≤ b) (hT : 0 ≤ T) :
    (k : ℂ) ∈ Rectangle (cotLowerCorner a T) (cotUpperCorner b T) ↔
      k ∈ Finset.Ioc a b := by
  have hab'' : (a : ℝ) ≤ b := by exact_mod_cast hab
  simp only [Rectangle, mem_reProdIm, cotLowerCorner, cotUpperCorner,
    sub_re, add_re, intCast_re, div_ofNat_re, one_re, mul_re, ofReal_re, I_re,
    ofReal_im, I_im, mul_zero, zero_mul, sub_zero, add_zero,
    sub_im, add_im, intCast_im, div_ofNat_im, one_im, mul_im, zero_div,
    mul_one, zero_add, zero_sub]
  rw [Set.uIcc_of_le (by linarith : (a : ℝ) + 1 / 2 ≤ b + 1 / 2),
    Set.uIcc_of_le (by linarith : -T ≤ T)]
  simp only [Set.mem_Icc, int_mem_half_interval, Finset.mem_Ioc]
  exact and_iff_left ⟨by linarith, hT⟩

lemma sin_pi_mul_ne_zero_cotBorder (a b : ℤ) (T : ℝ) (hT : 0 < T) :
    ∀ s ∈ RectangleBorder (cotLowerCorner a T) (cotUpperCorner b T),
      Complex.sin (Real.pi * s) ≠ 0 := by
  intro s hs hz
  obtain ⟨k, rfl⟩ := (sin_pi_mul_eq_zero_iff_integer s).mp hz
  simp only [RectangleBorder, Set.mem_union, mem_reProdIm, Set.mem_singleton_iff,
    cotLowerCorner, cotUpperCorner, sub_re, add_re, intCast_re, div_ofNat_re,
    one_re, mul_re, ofReal_re, I_re, ofReal_im, I_im, mul_zero, zero_mul,
    sub_zero, add_zero, sub_im, add_im, intCast_im, div_ofNat_im, one_im,
    mul_im, zero_div, mul_one, zero_add, zero_sub] at hs
  rcases hs with ((h | h) | h) | h
  · linarith [h.2]
  · exact int_ne_half_integer a k h.1
  · linarith [h.2]
  · exact int_ne_half_integer b k h.1

lemma rectangleIntegralPrime_pi_cot_integer_sum (a b : ℤ) (T : ℝ)
    (hab : a ≤ b) (hT : 0 < T) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (Rectangle (cotLowerCorner a T) (cotUpperCorner b T))) :
    RectangleIntegral' (fun s => g s * (Real.pi * Complex.cot (Real.pi * s)))
      (cotLowerCorner a T) (cotUpperCorner b T) =
        ∑ k ∈ Finset.Ioc a b, g (k : ℂ) := by
  classical
  let Z := (Finset.Ioc a b).image (fun k : ℤ => (k : ℂ))
  have hre : (cotLowerCorner a T).re ≤ (cotUpperCorner b T).re := by
    simpa [cotLowerCorner, cotUpperCorner] using (show (a : ℝ) ≤ b by exact_mod_cast hab)
  have him : (cotLowerCorner a T).im ≤ (cotUpperCorner b T).im := by
    simpa [cotLowerCorner, cotUpperCorner] using (show -T ≤ T by linarith)
  have hZ : ∀ s ∈ Rectangle (cotLowerCorner a T) (cotUpperCorner b T),
      Complex.sin (Real.pi * s) = 0 ↔ s ∈ Z := by
    intro s hs
    rw [sin_pi_mul_eq_zero_iff_integer]
    constructor
    · rintro ⟨k, rfl⟩
      exact Finset.mem_image.mpr ⟨k, (int_mem_cotRectangle a b k T hab hT.le).mp hs, rfl⟩
    · intro h
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
      exact ⟨k, rfl⟩
  have hZsub : (Z : Set ℂ) ⊆ Rectangle (cotLowerCorner a T) (cotUpperCorner b T) := by
    intro s hs
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hs
    exact (int_mem_cotRectangle a b k T hab hT.le).mpr hk
  rw [rectangleIntegralPrime_pi_cot hre him Z hg
    (sin_pi_mul_ne_zero_cotBorder a b T hT) hZ hZsub]
  exact Finset.sum_image (by
    intro k hk l hl hkl
    exact Int.cast_injective (α := ℂ) hkl)

end ZudilinZeta
end
end


-- Source module: missions.zudilin.ExponentialEnvelope
section
set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory Set

namespace ZudilinZeta

lemma integrable_abs_pow_mul_exp_neg_abs (k : ℕ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ => |t| ^ k * Real.exp (-c * |t|)) := by
  have hi : IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-c * t)) (Ioi 0) := by
    simpa only [Real.rpow_natCast, Real.rpow_one] using
      integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := 1) (s := (k : ℝ)) (b := c)
        (by linarith [Nat.cast_nonneg (α := ℝ) k]) zero_lt_one hc
  have hp : IntegrableOn (fun t : ℝ => |t| ^ k * Real.exp (-c * |t|)) (Ioi 0) := by
    apply hi.congr_fun _ measurableSet_Ioi
    intro t ht
    simp only [abs_of_pos (mem_Ioi.mp ht)]
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, hp⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding]
  simpa only [Function.comp_def, abs_neg, neg_preimage, neg_Iio, neg_zero] using hp

lemma integrable_one_add_abs_pow_mul_exp_neg_abs (k : ℕ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ => (1 + |t|) ^ k * Real.exp (-c * |t|)) := by
  have h0 : Integrable (fun t : ℝ => Real.exp (-c * |t|)) := by
    simpa using integrable_abs_pow_mul_exp_neg_abs 0 hc
  have hk := integrable_abs_pow_mul_exp_neg_abs k hc
  apply ((h0.add hk).const_mul ((2 : ℝ) ^ (k - 1))).mono'
  · exact (by fun_prop : Continuous (fun t : ℝ =>
      (1 + |t|) ^ k * Real.exp (-c * |t|))).aestronglyMeasurable
  · apply ae_of_all
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hb := mul_le_mul_of_nonneg_right
      (add_pow_le (a := (1 : ℝ)) (b := |t|) zero_le_one (abs_nonneg t) k)
      (Real.exp_pos (-c * |t|)).le
    simpa only [Pi.add_apply, one_pow, add_mul, one_mul, mul_assoc] using hb

lemma integrable_polynomial_phase_envelope {H : ℝ → ℝ}
    (hH : Measurable H) {c C A : ℝ} (hc : 0 < c) (hA : 0 ≤ A) (k : ℕ)
    (hdecay : ∀ t, H t ≤ C - c * |t|) :
    Integrable (fun t : ℝ => A * (1 + |t|) ^ k * Real.exp (H t / 2)) := by
  have hi := (integrable_one_add_abs_pow_mul_exp_neg_abs k (half_pos hc)).const_mul
    (A * Real.exp (C / 2))
  apply hi.mono'
  · apply Measurable.aestronglyMeasurable
    exact (measurable_const.mul ((measurable_const.add measurable_id.abs).pow_const k)).mul
      ((hH.div_const 2).exp)
  · apply ae_of_all
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      A * (1 + |t|) ^ k * Real.exp (H t / 2) ≤
          A * (1 + |t|) ^ k * Real.exp ((C - c * |t|) / 2) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hdecay t]))
        positivity
      _ = (A * Real.exp (C / 2)) * ((1 + |t|) ^ k * Real.exp (-(c / 2) * |t|)) := by
        rw [show (C - c * |t|) / 2 = C / 2 + -(c / 2) * |t| by ring, Real.exp_add]
        ring

end ZudilinZeta
end


-- Source module: missions.zudilin.Params13ContourBounds
section
set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology MeasureTheory

namespace ZudilinZeta

def params13ContourIntegrand (n : ℕ) (s : ℂ) : ℂ :=
  complexRationalR params13 n (-s) * cubicCotKernel s

def cotEnvelope (y : ℝ) : ℝ := 64 * Real.pi ^ 3 * Real.exp (-2 * Real.pi * |y|)

lemma cotEnvelope_nonneg (y : ℝ) : 0 ≤ cotEnvelope y := by unfold cotEnvelope; positivity

lemma integrable_cotEnvelope : Integrable cotEnvelope := by
  have h := (integrable_abs_pow_mul_exp_neg_abs 0
    (show (0 : ℝ) < 2 * Real.pi by positivity)).const_mul (64 * Real.pi ^ 3)
  change Integrable (fun y : ℝ => 64 * Real.pi ^ 3 * Real.exp (-2 * Real.pi * |y|))
  simpa only [pow_zero, one_mul, neg_mul, mul_assoc] using h

lemma sin_pi_mul_ne_zero_half_line (k : ℤ) (y : ℝ) :
    Complex.sin (Real.pi * ((k : ℂ) + 1 / 2 + (y : ℂ) * I)) ≠ 0 := by
  intro hs
  obtain ⟨j, hj⟩ := (sin_pi_mul_eq_zero_iff_integer _).mp hs
  have h := congrArg Complex.re hj
  simp only [add_re, intCast_re, div_ofNat_re, one_re, mul_re, ofReal_re,
    ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero] at h
  exact int_ne_half_integer k j h.symm

lemma params13_contour_envelopes (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    (∀ s : ℂ, 1 ≤ |s.im| →
      ‖params13ContourIntegrand n s‖ ≤ (C / |s.im|) * cotEnvelope s.im) ∧
    (∀ (k : ℤ) (y : ℝ), 62 * (n : ℝ) + 2 ≤ (k : ℝ) + 1 / 2 →
      ‖params13ContourIntegrand n ((k : ℂ) + 1 / 2 + (y : ℂ) * I)‖ ≤
        (C / ((k : ℝ) + 1 / 2 - (62 * n + 1))) * cotEnvelope y) := by
  obtain ⟨C, hC, hre, him⟩ := params13_rational_bounds n
  refine ⟨C, hC, ?_, ?_⟩
  · intro s hs
    rw [params13ContourIntegrand, norm_mul]
    exact mul_le_mul (him s hs) (norm_cubicCotKernel_horizontal s hs)
      (norm_nonneg _) (by positivity)
  · intro k y hk
    rw [params13ContourIntegrand, norm_mul]
    have h := hre ((k : ℂ) + 1 / 2 + (y : ℂ) * I) (by simpa using hk)
    simpa only [cotEnvelope, add_re, intCast_re, div_ofNat_re, one_re, mul_re, ofReal_re,
      ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero] using!
      mul_le_mul h (norm_cubicCotKernel_half_integer k y) (norm_nonneg _)
        (show 0 ≤ C / (((k : ℂ) + 1 / 2 + (y : ℂ) * I).re - (62 * (n : ℝ) + 1)) by
          simp only [add_re, intCast_re, div_ofNat_re, one_re, mul_re, ofReal_re,
            ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]
          apply div_nonneg hC
          linarith)

lemma integrable_params13_contour_half_line (n : ℕ) (k : ℤ)
    (hk : 62 * (n : ℝ) + 2 ≤ (k : ℝ) + 1 / 2) :
    Integrable (fun y : ℝ => params13ContourIntegrand n ((k : ℂ) + 1 / 2 + (y : ℂ) * I)) := by
  obtain ⟨C, hC, hh, hv⟩ := params13_contour_envelopes n
  apply (integrable_cotEnvelope.const_mul (C / ((k : ℝ) + 1 / 2 - (62 * n + 1)))).mono'
  · apply Continuous.aestronglyMeasurable
    apply continuous_iff_continuousAt.mpr
    intro y
    have hr := analyticAt_params13_neg_rational n ((k : ℂ) + 1 / 2 + (y : ℂ) * I)
      (by simp; linarith)
    have hc := analyticAt_cubicCotKernel _ (sin_pi_mul_ne_zero_half_line k y)
    have hp : ContinuousAt (fun t : ℝ => (k : ℂ) + 1 / 2 + (t : ℂ) * I) y := by fun_prop
    simpa only [params13ContourIntegrand, Function.comp_def, Pi.mul_apply] using!
      (hr.mul hc).continuousAt.comp (x := y) hp
  · exact ae_of_all _ (fun y => hv k y hk)

lemma norm_intervalIntegral_le_cotEnvelope {f : ℝ → ℂ} {B a b : ℝ}
    (hB : 0 ≤ B) (hab : a ≤ b) (hf : ∀ y, ‖f y‖ ≤ B * cotEnvelope y) :
    ‖∫ y in a..b, f y‖ ≤ B * ∫ y : ℝ, cotEnvelope y := by
  calc
    _ ≤ ∫ y in a..b, B * cotEnvelope y :=
      intervalIntegral.norm_integral_le_of_norm_le hab
        (ae_of_all _ (fun y _ => hf y))
        (integrable_cotEnvelope.const_mul B).intervalIntegrable
    _ ≤ ∫ y : ℝ, B * cotEnvelope y := by
      rw [intervalIntegral.integral_of_le hab]
      apply setIntegral_le_integral (integrable_cotEnvelope.const_mul B)
      exact ae_of_all _ (fun y => mul_nonneg hB (cotEnvelope_nonneg y))
    _ = _ := MeasureTheory.integral_const_mul _ _

end ZudilinZeta
end
end


-- Source module: missions.zudilin.Params13PhysicalKernel
section
set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology MeasureTheory

namespace ZudilinZeta

def params13PhysicalCos (n : ℕ) (s : ℂ) : ℂ :=
  params13GammaKernel n (s / (n : ℂ)) * Complex.cos (Real.pi * s)

lemma params13_contour_eq_physicalCos (n : ℕ) (hn : 0 < n) (s : ℂ) (hs : s.im ≠ 0) :
    params13ContourIntegrand n s = (-1 : ℂ) ^ (n + 1) * params13PhysicalCos n s := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have h := params13_cubic_sine_kernel n (s / (n : ℂ))
    (by simpa only [mul_div_cancel₀ _ hn'] using hs)
  simpa only [params13ContourIntegrand, cubicCotKernel, params13PhysicalCos,
    mul_div_cancel₀ _ hn', mul_assoc] using h

lemma norm_params13_physicalCos (n : ℕ) (hn : 0 < n) (s : ℂ) (hs : s.im ≠ 0) :
    ‖params13PhysicalCos n s‖ = ‖params13ContourIntegrand n s‖ := by
  rw [params13_contour_eq_physicalCos n hn s hs, norm_mul, norm_pow,
    norm_neg, norm_one, one_pow, one_mul]

lemma differentiableAt_params13PhysicalCos (n : ℕ) (hn : 2 ≤ n) (s : ℂ)
    (hs : 87 * (n : ℝ) ≤ s.re ∧ s.re ≤ (175 / 2) * n) :
    DifferentiableAt ℂ (params13PhysicalCos n) s := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsn : 87 ≤ (s / (n : ℂ)).re ∧ (s / (n : ℂ)).re ≤ 175 / 2 := by
    rw [Complex.div_natCast_re]
    exact ⟨(le_div_iff₀ hnp).mpr hs.1, (div_le_iff₀ hnp).mpr hs.2⟩
  have hdiv : DifferentiableAt ℂ (fun w : ℂ => w / (n : ℂ)) s := by fun_prop
  have hmul : DifferentiableAt ℂ (fun w : ℂ => (Real.pi : ℂ) * w) s := by fun_prop
  exact ((differentiableAt_params13GammaKernel n hn hsn).comp s hdiv).mul
    ((Complex.differentiableAt_cos).comp s hmul)

lemma continuous_params13PhysicalCos_vertical (n : ℕ) (hn : 2 ≤ n) (x : ℝ)
    (hx : 87 * (n : ℝ) ≤ x ∧ x ≤ (175 / 2) * n) :
    Continuous (fun y : ℝ => params13PhysicalCos n ((x : ℂ) + (y : ℂ) * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  have h := differentiableAt_params13PhysicalCos n hn ((x : ℂ) + (y : ℂ) * I)
    (by simpa using hx)
  have hp : ContinuousAt (fun t : ℝ => (x : ℂ) + (t : ℂ) * I) y := by fun_prop
  exact h.continuousAt.comp (x := y) hp

lemma params13_physicalCos_envelope (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 ≤ |s.im| →
      ‖params13PhysicalCos n s‖ ≤ C * cotEnvelope s.im := by
  obtain ⟨C, hC, hh, hv⟩ := params13_contour_envelopes n
  refine ⟨C, hC, fun s hs => ?_⟩
  have hsi : s.im ≠ 0 := by intro h; norm_num [h] at hs
  rw [norm_params13_physicalCos n (by omega) s hsi]
  exact (hh s hs).trans (mul_le_mul_of_nonneg_right (div_le_self hC hs) (cotEnvelope_nonneg _))

lemma integrable_of_continuous_cotEnvelope_tail {f : ℝ → ℂ} (hf : Continuous f) (B : ℝ)
    (hb : ∀ y : ℝ, 1 ≤ |y| → ‖f y‖ ≤ B * cotEnvelope y) : Integrable f := by
  rw [← integrableOn_univ, ← Set.union_compl_self (Set.Icc (-1 : ℝ) 1), integrableOn_union]
  refine ⟨hf.integrableOn_Icc, ?_⟩
  apply ((integrable_cotEnvelope.const_mul B).integrableOn).mono'
  · exact hf.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_Icc.compl)] with y hy
    apply hb
    by_contra h
    have ha := abs_lt.mp (lt_of_not_ge h)
    exact hy ⟨ha.1.le, ha.2.le⟩

lemma integrable_params13PhysicalCos_vertical (n : ℕ) (hn : 2 ≤ n) (x : ℝ)
    (hx : 87 * (n : ℝ) ≤ x ∧ x ≤ (175 / 2) * n) :
    Integrable (fun y : ℝ => params13PhysicalCos n ((x : ℂ) + (y : ℂ) * I)) := by
  obtain ⟨C, hC, hb⟩ := params13_physicalCos_envelope n hn
  apply integrable_of_continuous_cotEnvelope_tail
    (continuous_params13PhysicalCos_vertical n hn x hx) C
  intro y hy
  simpa using hb ((x : ℂ) + (y : ℂ) * I) (by simpa using hy)

end ZudilinZeta
end
end


-- Source module: missions.zudilin.Params13ContourBoundaryLimits
section
set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology MeasureTheory

namespace ZudilinZeta

lemma norm_params13_horizontal_le {n : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hh : ∀ s : ℂ, 1 ≤ |s.im| →
      ‖params13ContourIntegrand n s‖ ≤ (C / |s.im|) * cotEnvelope s.im)
    (a b y : ℝ) (hy : 1 ≤ |y|) :
    ‖HIntegral (params13ContourIntegrand n) a b y‖ ≤ C * cotEnvelope y * |b - a| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  have h := hh ((x : ℂ) + (y : ℂ) * I) (by simpa using hy)
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_one,
    mul_zero, add_zero, zero_add] at h
  have hd : C / |y| ≤ C := div_le_self hC hy
  simpa only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_one,
    mul_zero, add_zero, zero_add] using
    h.trans (mul_le_mul_of_nonneg_right hd (cotEnvelope_nonneg y))

lemma norm_params13_vertical_le {n : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ (k : ℤ) (y : ℝ), 62 * (n : ℝ) + 2 ≤ (k : ℝ) + 1 / 2 →
      ‖params13ContourIntegrand n ((k : ℂ) + 1 / 2 + (y : ℂ) * I)‖ ≤
        (C / ((k : ℝ) + 1 / 2 - (62 * n + 1))) * cotEnvelope y)
    (k : ℤ) (T : ℝ) (hT : 0 ≤ T) (hk : 62 * (n : ℝ) + 2 ≤ (k : ℝ) + 1 / 2) :
    ‖VIntegral (params13ContourIntegrand n) ((k : ℝ) + 1 / 2) (-T) T‖ ≤
      (C / ((k : ℝ) + 1 / 2 - (62 * n + 1))) * ∫ y : ℝ, cotEnvelope y := by
  rw [VIntegral, smul_eq_mul, norm_mul, Complex.norm_I, one_mul]
  apply norm_intervalIntegral_le_cotEnvelope
  · apply div_nonneg hC
    linarith
  · linarith
  · intro y
    simpa only [ofReal_add, ofReal_div, ofReal_one, ofReal_ofNat, ofReal_intCast] using hv k y hk

lemma params13_horizontal_integral_tendsto_zero (n : ℕ) (a b σ : ℝ) (hσ : |σ| = 1) :
    Tendsto (fun N : ℕ => HIntegral (params13ContourIntegrand n) a (b + N)
      (σ * ((N : ℝ) + 1))) atTop (𝓝 0) := by
  obtain ⟨C, hC, hh, hv⟩ := params13_contour_envelopes n
  have hbound (N : ℕ) :
      ‖HIntegral (params13ContourIntegrand n) a (b + N) (σ * ((N : ℝ) + 1))‖ ≤
        (C * (64 * Real.pi ^ 3)) *
          ((|b - a| + N) * Real.exp (-(2 * Real.pi) * ((N : ℝ) + 1))) := by
    have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have habs : |σ * ((N : ℝ) + 1)| = (N : ℝ) + 1 := by
      rw [abs_mul, hσ, one_mul, abs_of_nonneg (by linarith)]
    have hlength : |b + (N : ℝ) - a| ≤ |b - a| + N := by
      calc
        _ = |(b - a) + N| := by congr 1; ring
        _ ≤ |b - a| + |(N : ℝ)| := abs_add_le _ _
        _ = _ := by rw [abs_of_nonneg hn]
    have h := norm_params13_horizontal_le hC hh a (b + N) (σ * ((N : ℝ) + 1))
      (by rw [habs]; linarith)
    apply h.trans
    rw [cotEnvelope, habs]
    calc
      _ ≤ C * (64 * Real.pi ^ 3 * Real.exp (-2 * Real.pi * ((N : ℝ) + 1))) *
          (|b - a| + N) := mul_le_mul_of_nonneg_left hlength (by positivity)
      _ = _ := by ring
  apply squeeze_zero_norm hbound
  have ht : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds
  have h0 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (2 * Real.pi)
    (by positivity)).comp ht
  have h1 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (2 * Real.pi)
    (by positivity)).comp ht
  simp only [Function.comp_def, Real.rpow_zero, Real.rpow_one, one_mul] at h0 h1
  have h := ((h0.const_mul (|b - a| - 1)).add h1).const_mul (C * (64 * Real.pi ^ 3))
  convert h using 1
  · funext N
    ring
  · simp

lemma params13_right_integral_tendsto_zero (n : ℕ) (hn : 1 ≤ n) :
    Tendsto (fun N : ℕ => VIntegral (params13ContourIntegrand n)
      (91 * (n : ℝ) + 1 + N + 1 / 2) (-((N : ℝ) + 1)) ((N : ℝ) + 1))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hh, hv⟩ := params13_contour_envelopes n
  have hbound (N : ℕ) :
      ‖VIntegral (params13ContourIntegrand n) (91 * (n : ℝ) + 1 + N + 1 / 2)
        (-((N : ℝ) + 1)) ((N : ℝ) + 1)‖ ≤
      (C / ((N : ℝ) + (29 * n + 1 / 2))) * ∫ y : ℝ, cotEnvelope y := by
    have hk : 62 * (n : ℝ) + 2 ≤ (((91 * n + 1 + N : ℕ) : ℤ) : ℝ) + 1 / 2 := by
      have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) N]
    have h := norm_params13_vertical_le hC hv ((91 * n + 1 + N : ℕ) : ℤ)
      ((N : ℝ) + 1) (by positivity) hk
    push_cast at h
    convert h using 1 <;> congr 1 <;> ring
  apply squeeze_zero_norm hbound
  have ht : Tendsto (fun N : ℕ => (N : ℝ) + (29 * n + 1 / 2)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds
  simpa using (tendsto_const_nhds.div_atTop ht).mul_const (∫ y : ℝ, cotEnvelope y)

end ZudilinZeta
end
end


-- Source module: missions.zudilin.RectangleIntegrationByParts
section
set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology MeasureTheory intervalIntegral

namespace ZudilinZeta

lemma rectangleBorderIntegrable_of_continuousOn {f : ℂ → ℂ} {z w : ℂ}
    (hf : ContinuousOn f (RectangleBorder z w)) : RectangleBorderIntegrable f z w := by
  have hH (y : ℝ) (hy : y = z.im ∨ y = w.im) :
      IntervalIntegrable (fun t : ℝ => f ((t : ℂ) + y * I)) volume z.re w.re := by
    apply ContinuousOn.intervalIntegrable
    apply hf.comp (by fun_prop)
    intro t ht
    simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff,
      add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
      sub_zero, add_zero, add_im, mul_im, zero_add]
    rcases hy with h | h
    · exact Or.inl (Or.inl (Or.inl ⟨ht, h⟩))
    · exact Or.inl (Or.inr ⟨ht, h⟩)
  have hV (x : ℝ) (hx : x = z.re ∨ x = w.re) :
      IntervalIntegrable (fun t : ℝ => f ((x : ℂ) + t * I)) volume z.im w.im := by
    apply ContinuousOn.intervalIntegrable
    apply hf.comp (by fun_prop)
    intro t ht
    simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff,
      add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
      sub_zero, add_zero, add_im, mul_im, zero_add]
    rcases hx with h | h
    · exact Or.inl (Or.inl (Or.inr ⟨h, ht⟩))
    · exact Or.inr ⟨h, ht⟩
  exact ⟨hH _ (Or.inl rfl), hH _ (Or.inr rfl), hV _ (Or.inr rfl), hV _ (Or.inl rfl)⟩

lemma hIntegral_eq_sub_of_hasDerivAt {f f' : ℂ → ℂ} (a b y : ℝ)
    (hf : ∀ t ∈ uIcc a b, HasDerivAt f (f' ((t : ℂ) + y * I)) ((t : ℂ) + y * I))
    (hi : IntervalIntegrable (fun t : ℝ => f' ((t : ℂ) + y * I)) volume a b) :
    HIntegral f' a b y = f ((b : ℂ) + y * I) - f ((a : ℂ) + y * I) := by
  apply integral_eq_sub_of_hasDerivAt _ hi
  intro t ht
  convert! ((hf t ht).comp (t : ℂ)
    ((hasDerivAt_id (t : ℂ)).add_const ((y : ℂ) * I))).comp_ofReal using 1 <;> simp

lemma vIntegral_eq_sub_of_hasDerivAt {f f' : ℂ → ℂ} (x a b : ℝ)
    (hf : ∀ t ∈ uIcc a b, HasDerivAt f (f' ((x : ℂ) + t * I)) ((x : ℂ) + t * I))
    (hi : IntervalIntegrable (fun t : ℝ => f' ((x : ℂ) + t * I)) volume a b) :
    VIntegral f' x a b = f ((x : ℂ) + b * I) - f ((x : ℂ) + a * I) := by
  rw [VIntegral, smul_eq_mul, ← intervalIntegral.integral_const_mul]
  apply integral_eq_sub_of_hasDerivAt _ (hi.const_mul I)
  intro t ht
  convert! ((hf t ht).comp (t : ℂ)
    (((hasDerivAt_id (t : ℂ)).mul_const I).const_add (x : ℂ))).comp_ofReal
    using 1 <;> ring

lemma rectangleIntegral_eq_zero_of_hasDerivAt {f f' : ℂ → ℂ} {z w : ℂ}
    (hf : ∀ s ∈ RectangleBorder z w, HasDerivAt f (f' s) s)
    (hi : RectangleBorderIntegrable f' z w) :
    RectangleIntegral f' z w = 0 := by
  have hbot (t : ℝ) (ht : t ∈ uIcc z.re w.re) :
      (t : ℂ) + z.im * I ∈ RectangleBorder z w := by
    simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff,
      add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
      sub_zero, add_zero, add_im, mul_im, zero_add]
    exact Or.inl (Or.inl (Or.inl ⟨ht, trivial⟩))
  have htop (t : ℝ) (ht : t ∈ uIcc z.re w.re) :
      (t : ℂ) + w.im * I ∈ RectangleBorder z w := by
    simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff,
      add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
      sub_zero, add_zero, add_im, mul_im, zero_add]
    exact Or.inl (Or.inr ⟨ht, trivial⟩)
  have hleft (t : ℝ) (ht : t ∈ uIcc z.im w.im) :
      (z.re : ℂ) + t * I ∈ RectangleBorder z w := by
    simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff,
      add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
      sub_zero, add_zero, add_im, mul_im, zero_add]
    exact Or.inl (Or.inl (Or.inr ⟨trivial, ht⟩))
  have hright (t : ℝ) (ht : t ∈ uIcc z.im w.im) :
      (w.re : ℂ) + t * I ∈ RectangleBorder z w := by
    simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff,
      add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
      sub_zero, add_zero, add_im, mul_im, zero_add]
    exact Or.inr ⟨trivial, ht⟩
  rw [RectangleIntegral,
    hIntegral_eq_sub_of_hasDerivAt _ _ _ (fun t ht => hf _ (hbot t ht)) hi.1,
    hIntegral_eq_sub_of_hasDerivAt _ _ _ (fun t ht => hf _ (htop t ht)) hi.2.1,
    vIntegral_eq_sub_of_hasDerivAt _ _ _ (fun t ht => hf _ (hright t ht)) hi.2.2.1,
    vIntegral_eq_sub_of_hasDerivAt _ _ _ (fun t ht => hf _ (hleft t ht)) hi.2.2.2]
  ring

lemma rectangleIntegral_sub {f g : ℂ → ℂ} {z w : ℂ}
    (hf : RectangleBorderIntegrable f z w) (hg : RectangleBorderIntegrable g z w) :
    RectangleIntegral (fun s => f s - g s) z w =
      RectangleIntegral f z w - RectangleIntegral g z w := by
  simp only [RectangleIntegral, HIntegral, VIntegral,
    intervalIntegral.integral_sub hf.1 hg.1,
    intervalIntegral.integral_sub hf.2.1 hg.2.1,
    intervalIntegral.integral_sub hf.2.2.1 hg.2.2.1,
    intervalIntegral.integral_sub hf.2.2.2 hg.2.2.2, smul_eq_mul]
  ring

lemma rectangleIntegral_const_mul (c : ℂ) (f : ℂ → ℂ) (z w : ℂ) :
    RectangleIntegral (fun s => c * f s) z w = c * RectangleIntegral f z w := by
  simp only [RectangleIntegral, HIntegral, VIntegral,
    intervalIntegral.integral_const_mul, smul_eq_mul]
  ring

lemma rectangleIntegral_second_derivative_transfer
    {u u' u'' v v' v'' : ℂ → ℂ} {z w : ℂ}
    (hu : ∀ s ∈ RectangleBorder z w, HasDerivAt u (u' s) s)
    (hu' : ∀ s ∈ RectangleBorder z w, HasDerivAt u' (u'' s) s)
    (hv : ∀ s ∈ RectangleBorder z w, HasDerivAt v (v' s) s)
    (hv' : ∀ s ∈ RectangleBorder z w, HasDerivAt v' (v'' s) s)
    (hi : RectangleBorderIntegrable (fun s => u'' s * v s) z w)
    (hj : RectangleBorderIntegrable (fun s => u s * v'' s) z w) :
    RectangleIntegral (fun s => u'' s * v s) z w =
      RectangleIntegral (fun s => u s * v'' s) z w := by
  have h := rectangleIntegral_eq_zero_of_hasDerivAt
    (f := fun s => u' s * v s - u s * v' s)
    (f' := fun s => u'' s * v s - u s * v'' s)
    (fun s hs => ?_)
    ⟨hi.1.sub hj.1, hi.2.1.sub hj.2.1,
      hi.2.2.1.sub hj.2.2.1, hi.2.2.2.sub hj.2.2.2⟩
  · rw [rectangleIntegral_sub hi hj] at h
    exact sub_eq_zero.mp h
  · convert! ((hu' s hs).mul (hv s hs)).sub ((hu s hs).mul (hv' s hs)) using 1 <;> ring

end ZudilinZeta
end
end


-- Source module: missions.zudilin.CubicCotangentResidues
section
set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology

namespace ZudilinZeta

lemma rectangleBorder_subset_rectangle (z w : ℂ) : RectangleBorder z w ⊆ Rectangle z w := by
  intro s hs
  simp only [RectangleBorder, Set.mem_union, mem_reProdIm, Set.mem_singleton_iff] at hs
  change s.re ∈ uIcc z.re w.re ∧ s.im ∈ uIcc z.im w.im
  rcases hs with ((h | h) | h) | h
  · exact ⟨h.1, h.2 ▸ left_mem_uIcc⟩
  · exact ⟨h.1 ▸ left_mem_uIcc, h.2⟩
  · exact ⟨h.1, h.2 ▸ right_mem_uIcc⟩
  · exact ⟨h.1 ▸ right_mem_uIcc, h.2⟩

lemma rectangleIntegral_cubic_transfer {f : ℂ → ℂ} {z w : ℂ}
    (hf : ∀ s ∈ RectangleBorder z w, AnalyticAt ℂ f s)
    (hs : ∀ s ∈ RectangleBorder z w, Complex.sin (Real.pi * s) ≠ 0) :
    RectangleIntegral (fun s => iteratedDeriv 2 f s * piCot s) z w =
      2 * RectangleIntegral (fun s => f s * cubicCotKernel s) z w := by
  have hf2 (s : ℂ) (h : s ∈ RectangleBorder z w) :
      AnalyticAt ℂ (iteratedDeriv 2 f) s := by
    rw [iteratedDeriv_eq_iterate]
    exact (hf s h).iterated_deriv 2
  have hi : RectangleBorderIntegrable (fun s => iteratedDeriv 2 f s * piCot s) z w :=
    rectangleBorderIntegrable_of_continuousOn (fun s h =>
      ((hf2 s h).continuousAt.mul (analyticAt_piCot s (hs s h)).continuousAt).continuousWithinAt)
  have hj : RectangleBorderIntegrable (fun s => f s * (2 * cubicCotKernel s)) z w :=
    rectangleBorderIntegrable_of_continuousOn (fun s h =>
      ((hf s h).continuousAt.mul
        (continuousAt_const.mul (analyticAt_cubicCotKernel s (hs s h)).continuousAt)).continuousWithinAt)
  have h := rectangleIntegral_second_derivative_transfer
    (u := f) (u' := deriv f) (u'' := iteratedDeriv 2 f)
    (v := piCot) (v' := piCotD) (v'' := fun s => 2 * cubicCotKernel s)
    (fun s h => (hf s h).differentiableAt.hasDerivAt)
    (fun s h => by
      simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using!
        (hf s h).deriv.differentiableAt.hasDerivAt)
    (fun s h => hasDerivAt_piCot s (hs s h))
    (fun s h => hasDerivAt_piCotD s (hs s h)) hi hj
  rw [show (fun s => f s * (2 * cubicCotKernel s)) =
    (fun s => (2 : ℂ) * (f s * cubicCotKernel s)) by funext s; ring,
    rectangleIntegral_const_mul] at h
  exact h

lemma rectangleIntegralPrime_cubic_integer_sum (a b : ℤ) (T : ℝ)
    (hab : a ≤ b) (hT : 0 < T) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Rectangle (cotLowerCorner a T) (cotUpperCorner b T))) :
    RectangleIntegral' (fun s => f s * cubicCotKernel s)
      (cotLowerCorner a T) (cotUpperCorner b T) =
        (1 / 2 : ℂ) * ∑ k ∈ Finset.Ioc a b, iteratedDeriv 2 f (k : ℂ) := by
  have hres := rectangleIntegralPrime_pi_cot_integer_sum a b T hab hT
    (g := iteratedDeriv 2 f) (fun s h => by
      rw [iteratedDeriv_eq_iterate]
      exact (hf s h).iterated_deriv 2)
  have htransfer := rectangleIntegral_cubic_transfer
    (fun s h => hf s (rectangleBorder_subset_rectangle _ _ h))
    (sin_pi_mul_ne_zero_cotBorder a b T hT)
  change (1 / (2 * (Real.pi : ℂ) * I)) *
    RectangleIntegral (fun s => iteratedDeriv 2 f s * piCot s) _ _ = _ at hres
  rw [htransfer] at hres
  change (1 / (2 * (Real.pi : ℂ) * I)) *
    RectangleIntegral (fun s => f s * cubicCotKernel s) _ _ = _
  rw [← hres]
  ring

end ZudilinZeta
end
end


-- Source module: missions.zudilin.ComplexRationalDerivatives
section
set_option autoImplicit false
noncomputable section
open Complex Filter Topology

namespace ZudilinZeta

lemma deriv_complex_of_eventually_real {f : ℂ → ℂ} {g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℂ f (x : ℂ))
    (he : (fun t : ℝ => f (t : ℂ)) =ᶠ[𝓝 x] (fun t => (g t : ℂ))) :
    deriv f (x : ℂ) = ((deriv g x : ℝ) : ℂ) := by
  have hd := hf.hasDerivAt
  have hg : HasDerivAt g (deriv f (x : ℂ)).re x := by
    apply hd.real_of_complex.congr_of_eventuallyEq
    filter_upwards [he] with t ht
    simpa using (congrArg Complex.re ht).symm
  have hc : HasDerivAt (fun t : ℝ => f (t : ℂ))
      ((deriv f (x : ℂ)).re : ℂ) x :=
    hg.ofReal_comp.congr_of_eventuallyEq he
  rw [hg.deriv]
  exact hd.comp_ofReal.unique hc

lemma iteratedDeriv_complex_of_real_interval {f : ℂ → ℂ} {g : ℝ → ℝ} (a : ℝ)
    (hf : ∀ x : ℝ, a < x → AnalyticAt ℂ f (x : ℂ))
    (he : ∀ x : ℝ, a < x → f (x : ℂ) = (g x : ℂ))
    (k : ℕ) (x : ℝ) (hx : a < x) :
    iteratedDeriv k f (x : ℂ) = ((iteratedDeriv k g x : ℝ) : ℂ) := by
  induction k generalizing x with
  | zero => exact he x hx
  | succ k ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    apply deriv_complex_of_eventually_real
    · simpa only [iteratedDeriv_eq_iterate] using
        ((hf x hx).iterated_deriv k).differentiableAt
    · filter_upwards [eventually_gt_nhds hx] with t ht
      exact ih t ht

lemma iteratedDeriv_complexRationalR_ofReal (P : Params) (n k : ℕ) (t : ℝ)
    (ht : -1 < t) :
    iteratedDeriv k (complexRationalR P n) (t : ℂ) =
      ((iteratedDeriv k (R P n) t : ℝ) : ℂ) := by
  apply iteratedDeriv_complex_of_real_interval (-1)
  · intro x hx
    exact analyticAt_complexRationalR P n (x : ℂ)
      (pfDenominator_nonzero_right P n (x : ℂ) (by simpa using hx))
  · exact complexRationalR_ofReal P n
  · exact ht

end ZudilinZeta
end
end


-- Source module: missions.zudilin.PartialFractionContinuation
section
set_option autoImplicit false
open Polynomial Finset Filter
open scoped Topology
namespace ZudilinZeta

lemma cs_hh_mono (P : Params) (n : ℕ) {i j : ℕ}
    (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ P.q) : hh P n i ≤ hh P n j := by
  have he := aux_zz_eta_mono P (j-i) i hi (by omega)
  rw [show i+(j-i)=j by omega] at he
  simp only [hh, if_neg (show i ≠ 0 by omega), if_neg (show j ≠ 0 by omega)]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right n he) 1

lemma cs_numerator_zero_factor (P : Params) (n u : ℕ)
    (hu : u ∈ Ico 1 (hh P n 1)) : (X+C (u : ℚ))^P.r ∣ pfNumerator P n := by
  classical
  have hqr := P.q_ge
  have hd (j : ℕ) (hj : j ∈ Icc 1 P.r) :
      X+C (u : ℚ) ∣ C (1/((hh P n j-1).factorial : ℚ))*pfInterval 1 (hh P n j) := by
    have hj' := mem_Icc.mp hj
    have hm := cs_hh_mono P n (i := 1) (j := j) le_rfl hj'.1 (by omega)
    have huj : u ∈ Ico 1 (hh P n j) := mem_Ico.mpr ⟨(mem_Ico.mp hu).1,
      (mem_Ico.mp hu).2.trans_le hm⟩
    exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun k : ℕ => X+C (k : ℚ)) huj) _
  have hprod := Finset.prod_dvd_prod_of_dvd (fun _j => X+C (u : ℚ))
    (fun j => C (1/((hh P n j-1).factorial : ℚ))*pfInterval 1 (hh P n j)) hd
  simp only [prod_const, Nat.card_Icc, Nat.add_sub_cancel] at hprod
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hprod _) _) _

lemma cs_denominator_nonzero (P : Params) (n u : ℕ)
    (hu : u < hh P n 1) : (pfDenominator P n).eval₂ (algebraMap ℚ ℝ) (-(u : ℝ)) ≠ 0 := by
  classical
  simp only [pfDenominator, eval₂_finsetProd, pfInterval_eval]
  apply prod_ne_zero_iff.mpr
  intro j hj
  apply prod_ne_zero_iff.mpr
  intro k hk
  have hj' := mem_Icc.mp hj
  have hm := cs_hh_mono P n (i := 1) (j := j) le_rfl (by omega) hj'.2
  have huk : u < k := hu.trans_le (hm.trans (mem_Ico.mp hk).1)
  have huk' : (u : ℝ) < k := by exact_mod_cast huk
  linarith


end ZudilinZeta
end


-- Source module: missions.zudilin.ContourIntegerDerivatives
section
set_option autoImplicit false
noncomputable section
open Complex Polynomial Finset Filter Topology

namespace ZudilinZeta

lemma complexRationalR_derivative_zero (P : Params) (n u : ℕ)
    (hu : u ∈ Ico 1 (hh P n 1)) :
    iteratedDeriv (P.r - 1) (complexRationalR P n) (-(u : ℂ)) = 0 := by
  have hB : (pfDenominator P n).eval₂ (algebraMap ℚ ℂ) (-(u : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, polynomial_eval₂_complex_ofReal]
    exact Complex.ofReal_ne_zero.mpr (cs_denominator_nonzero P n u (mem_Ico.mp hu).2)
  have hf := analyticAt_complexRationalR P n (-(u : ℂ)) hB
  obtain ⟨Q, hQ⟩ := cs_numerator_zero_factor P n u hu
  have horder : (P.r : ℕ∞) ≤ analyticOrderAt (complexRationalR P n) (-(u : ℂ)) := by
    apply (natCast_le_analyticOrderAt hf).mpr
    refine ⟨fun z => Q.eval₂ (algebraMap ℚ ℂ) z /
      (pfDenominator P n).eval₂ (algebraMap ℚ ℂ) z,
      (analyticAt_id.aeval_polynomial Q).div
        (analyticAt_id.aeval_polynomial (pfDenominator P n)) hB, ?_⟩
    apply Filter.Eventually.of_forall
    intro z
    simp only [complexRationalR, hQ, eval₂_mul, eval₂_pow, eval₂_add, eval₂_X,
      eval₂_C, map_natCast, eval₂_natCast, sub_neg_eq_add, smul_eq_mul]
    ring
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf).mp horder
    (P.r - 1) (by have := P.r_odd.pos; omega)

lemma params13_second_derivative_zero_upper (n k : ℕ) (hn : 1 ≤ n)
    (hklo : 87 * n ≤ k) (hkhi : k < 91 * n + 2) :
    iteratedDeriv 2 (complexRationalR params13 n) (-(k : ℂ)) = 0 := by
  let u := 91 * n + 2 - k
  have hu : u ∈ Ico 1 (hh params13 n 1) := by
    simp only [mem_Ico, hh, params13, eta13, Nat.one_ne_zero, if_false,
      Nat.reduceLeDiff, if_true]
    dsimp [u]
    omega
  have hz : iteratedDeriv 2 (complexRationalR params13 n) (-(u : ℂ)) = 0 := by
    simpa [params13] using complexRationalR_derivative_zero params13 n u hu
  have href := complexRationalR_second_reflect params13 n (-(u : ℂ))
  have he : -(hh params13 n 0 : ℂ) - -(u : ℂ) = -(k : ℂ) := by
    simp only [hh, params13, if_pos rfl, eta13, u]
    rw [Nat.cast_sub (by omega : k ≤ 91 * n + 2)]
    push_cast
    ring
  simpa only [he, hz, neg_zero] using href

lemma params13_second_derivative_tail (n m : ℕ) :
    iteratedDeriv 2 (complexRationalR params13 n) (-((91 * n + 2 + m : ℕ) : ℂ)) =
      -((iteratedDeriv 2 (R params13 n) (m : ℝ) : ℝ) : ℂ) := by
  have href := complexRationalR_second_reflect params13 n (m : ℂ)
  rw [show (m : ℂ) = ((m : ℝ) : ℂ) by simp,
    iteratedDeriv_complexRationalR_ofReal params13 n 2 (m : ℝ)
      (by linarith [Nat.cast_nonneg (α := ℝ) m])] at href
  have he : -(hh params13 n 0 : ℂ) - ((m : ℝ) : ℂ) =
      -((91 * n + 2 + m : ℕ) : ℂ) := by
    simp [hh, params13, eta13]
    ring
  simpa only [he] using href

end ZudilinZeta
end
end


-- Source module: missions.zudilin.Params13FiniteContour
section
set_option autoImplicit false
noncomputable section
open Complex Finset Set Filter Topology

namespace ZudilinZeta

lemma sum_int_Ioc_nat_range (a N : ℕ) (f : ℤ → ℂ) :
    (∑ k ∈ Finset.Ioc (a : ℤ) ((a + N : ℕ) : ℤ), f k) =
      ∑ m ∈ Finset.range N, f ((a + 1 + m : ℕ) : ℤ) := by
  symm
  apply Finset.sum_bij (fun m _ => ((a + 1 + m : ℕ) : ℤ))
  · intro m hm
    simp only [Finset.mem_range] at hm
    simp only [Finset.mem_Ioc]
    constructor <;> omega
  · intro m hm j hj he
    omega
  · intro k hk
    simp only [Finset.mem_Ioc] at hk
    refine ⟨(k - a - 1).toNat, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro m hm
    rfl

lemma params13_residue_partial_sum (n M : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ Finset.Ioc ((87 * n : ℕ) : ℤ) ((91 * n + 1 + M : ℕ) : ℤ),
      iteratedDeriv 2 (fun s : ℂ => complexRationalR params13 n (-s)) (k : ℂ)) =
      -∑ m ∈ Finset.range M, ((iteratedDeriv 2 (R params13 n) (m : ℝ) : ℝ) : ℂ) := by
  have hr : 91 * n + 1 + M = 87 * n + (4 * n + 1 + M) := by omega
  rw [hr, sum_int_Ioc_nat_range, Finset.sum_range_add]
  have hz : (∑ m ∈ Finset.range (4 * n + 1),
      iteratedDeriv 2 (fun s : ℂ => complexRationalR params13 n (-s))
        (((87 * n + 1 + m : ℕ) : ℤ) : ℂ)) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    simp only [Finset.mem_range] at hm
    simp only [iteratedDeriv_comp_neg, neg_one_sq, one_smul, Int.cast_natCast]
    exact params13_second_derivative_zero_upper n (87 * n + 1 + m) hn (by omega) (by omega)
  rw [hz, zero_add, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [iteratedDeriv_comp_neg, neg_one_sq, one_smul, Int.cast_natCast]
  rw [show 87 * n + 1 + (4 * n + 1 + m) = 91 * n + 2 + m by omega]
  exact params13_second_derivative_tail n m

lemma params13_finite_contour (n M : ℕ) (hn : 1 ≤ n) (T : ℝ) (hT : 0 < T) :
    RectangleIntegral' (fun s => complexRationalR params13 n (-s) * cubicCotKernel s)
      (cotLowerCorner ((87 * n : ℕ) : ℤ) T)
      (cotUpperCorner ((91 * n + 1 + M : ℕ) : ℤ) T) =
        -(1 / 2 : ℂ) *
          ∑ m ∈ Finset.range M, ((iteratedDeriv 2 (R params13 n) (m : ℝ) : ℝ) : ℂ) := by
  have hab : ((87 * n : ℕ) : ℤ) ≤ ((91 * n + 1 + M : ℕ) : ℤ) := by omega
  have hf : AnalyticOnNhd ℂ (fun s => complexRationalR params13 n (-s))
      (Rectangle (cotLowerCorner ((87 * n : ℕ) : ℤ) T)
        (cotUpperCorner ((91 * n + 1 + M : ℕ) : ℤ) T)) := by
    intro s hs
    apply analyticAt_params13_neg_rational
    have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hab' : (87 : ℝ) * n + 1 / 2 ≤ 91 * n + 1 + M + 1 / 2 := by
      have := Nat.cast_nonneg (α := ℝ) M
      linarith
    have hre := (Complex.mem_reProdIm.mp hs).1
    simp only [cotLowerCorner, cotUpperCorner, sub_re, add_re, intCast_re,
      Int.cast_natCast, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one,
      div_ofNat_re, one_re, mul_re, ofReal_re, I_re, ofReal_im, I_im,
      mul_zero, zero_mul, sub_zero, add_zero] at hre
    push_cast at hre
    rw [Set.uIcc_of_le hab'] at hre
    linarith [hre.1]
  rw [rectangleIntegralPrime_cubic_integer_sum _ _ T hab hT hf,
    params13_residue_partial_sum n M hn]
  ring

end ZudilinZeta
end
end


-- Source module: missions.zudilin.Params13CubicContourIntegral
section
set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology MeasureTheory

namespace ZudilinZeta

lemma params13_cubic_contour_integral (n : ℕ) (hn : 1 ≤ n) :
    (∫ y : ℝ, params13ContourIntegrand n (87 * (n : ℂ) + 1 / 2 + (y : ℂ) * I)) =
      (2 * Real.pi : ℂ) * (F params13 n : ℂ) := by
  let J : ℂ := ∫ y : ℝ, params13ContourIntegrand n (87 * (n : ℂ) + 1 / 2 + (y : ℂ) * I)
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hi : Integrable (fun y : ℝ =>
      params13ContourIntegrand n (87 * (n : ℂ) + 1 / 2 + (y : ℂ) * I)) := by
    have h := integrable_params13_contour_half_line n ((87 * n : ℕ) : ℤ)
      (by push_cast; linarith)
    simpa using h
  have ht : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds
  have hleft := (intervalIntegral_tendsto_integral hi (tendsto_neg_atTop_atBot.comp ht) ht).const_mul I
  have hbot := params13_horizontal_integral_tendsto_zero n (87 * n + 1 / 2)
    (91 * n + 1 + 1 / 2) (-1) (by norm_num)
  have htop := params13_horizontal_integral_tendsto_zero n (87 * n + 1 / 2)
    (91 * n + 1 + 1 / 2) 1 (by norm_num)
  have hright := params13_right_integral_tendsto_zero n hn
  have hraw := (((hbot.sub htop).add hright).sub hleft).const_mul
    (1 / (2 * (Real.pi : ℂ) * I))
  have hcontour : Tendsto (fun N : ℕ =>
      RectangleIntegral' (params13ContourIntegrand n)
        (cotLowerCorner ((87 * n : ℕ) : ℤ) ((N : ℝ) + 1))
        (cotUpperCorner ((91 * n + 1 + N : ℕ) : ℤ) ((N : ℝ) + 1)))
      atTop (𝓝 ((1 / (2 * (Real.pi : ℂ) * I)) * (-(I * J)))) := by
    convert! hraw using 1
    · funext N
      simp only [RectangleIntegral, cotLowerCorner, cotUpperCorner, sub_re, add_re,
        intCast_re, div_ofNat_re, one_re, mul_re, ofReal_re, I_re, ofReal_im, I_im,
        mul_zero, zero_mul, sub_zero, add_zero, sub_im, add_im, intCast_im,
        div_ofNat_im, one_im, mul_im, zero_div, mul_one, zero_add, zero_sub,
        smul_eq_mul, neg_one_mul, one_mul]
      push_cast
      have he : (91 : ℝ) * n + 1 + N + 1 / 2 = 91 * n + 1 + 1 / 2 + N := by ring
      rw [he]
      simp only [VIntegral, smul_eq_mul, Function.comp_def, ofReal_add, ofReal_mul,
        ofReal_div, ofReal_ofNat, ofReal_natCast, ofReal_one]
    · simp only [sub_zero, add_zero, zero_sub, J]
  have hs : Summable (fun m : ℕ => iteratedDeriv 2 (R params13 n) (m : ℝ)) := by
    simpa [params13] using zudilin_series_summable params13 n (by omega)
  have hsum := ((Complex.hasSum_ofReal.mpr hs.hasSum).tendsto_sum_nat).const_mul (-(1 / 2 : ℂ))
  have hF : Tendsto (fun N : ℕ =>
      RectangleIntegral' (params13ContourIntegrand n)
        (cotLowerCorner ((87 * n : ℕ) : ℤ) ((N : ℝ) + 1))
        (cotUpperCorner ((91 * n + 1 + N : ℕ) : ℤ) ((N : ℝ) + 1)))
      atTop (𝓝 (-(F params13 n : ℂ))) := by
    have hsum' : Tendsto (fun N : ℕ => -(1 / 2 : ℂ) *
        ∑ m ∈ Finset.range N, ((iteratedDeriv 2 (R params13 n) (m : ℝ) : ℝ) : ℂ))
        atTop (𝓝 (-(F params13 n : ℂ))) := by
      convert! hsum using 1
      norm_num [F, params13, Complex.ofReal_mul, Complex.ofReal_tsum]
    apply hsum'.congr'
    filter_upwards [] with N
    exact (params13_finite_contour n N hn ((N : ℝ) + 1) (by positivity)).symm
  have he := tendsto_nhds_unique hcontour hF
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hp] at he
  change J = _
  linear_combination -he

end ZudilinZeta
end
end


-- Source module: missions.zudilin.VerticalContourShift
section
set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology MeasureTheory

namespace ZudilinZeta

lemma tendsto_cotEnvelope_nat :
    Tendsto (fun N : ℕ => cotEnvelope ((N : ℝ) + 1)) atTop (𝓝 0) := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds
  have h := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (2 * Real.pi)
    (by positivity)).comp ht).const_mul (64 * Real.pi ^ 3)
  convert! h using 1
  · funext N
    simp [cotEnvelope, abs_of_nonneg (show (0 : ℝ) ≤ N + 1 by positivity), mul_assoc]
  · simp

lemma vertical_integral_eq_of_strip (f : ℂ → ℂ) (a b C : ℝ)
    (hf : ∀ z : ℂ, z.re ∈ uIcc a b → DifferentiableAt ℂ f z)
    (ha : Integrable (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * I)))
    (hb : Integrable (fun y : ℝ => f ((b : ℂ) + (y : ℂ) * I)))
    (hbound : ∀ z : ℂ, 1 ≤ |z.im| → ‖f z‖ ≤ C * cotEnvelope z.im) :
    (∫ y : ℝ, f ((a : ℂ) + (y : ℂ) * I)) =
      ∫ y : ℝ, f ((b : ℂ) + (y : ℂ) * I) := by
  have hH (σ : ℝ) (hσ : |σ| = 1) :
      Tendsto (fun N : ℕ => HIntegral f a b (σ * ((N : ℝ) + 1))) atTop (𝓝 0) := by
    have hnorm (N : ℕ) : ‖HIntegral f a b (σ * ((N : ℝ) + 1))‖ ≤
        C * cotEnvelope ((N : ℝ) + 1) * |b - a| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      have hh : |σ * ((N : ℝ) + 1)| = (N : ℝ) + 1 := by
        rw [abs_mul, hσ, one_mul, abs_of_nonneg (by positivity)]
      have h := hbound ((x : ℂ) + ((σ * ((N : ℝ) + 1) : ℝ) : ℂ) * I)
        (by simpa only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
          mul_one, mul_zero, add_zero, zero_add, hh] using
          (show 1 ≤ (N : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) N]))
      simpa only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_one,
        mul_zero, add_zero, zero_add, cotEnvelope, hh,
        abs_of_nonneg (show (0 : ℝ) ≤ N + 1 by positivity)] using h
    apply squeeze_zero_norm hnorm
    simpa using (tendsto_cotEnvelope_nat.const_mul C).mul_const |b - a|
  have ht : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds
  have hVa := (intervalIntegral_tendsto_integral ha (tendsto_neg_atTop_atBot.comp ht) ht).const_mul I
  have hVb := (intervalIntegral_tendsto_integral hb (tendsto_neg_atTop_atBot.comp ht) ht).const_mul I
  have hlim := (((hH (-1) (by norm_num)).sub (hH 1 (by norm_num))).add hVb).sub hVa
  have hzero (N : ℕ) :
      HIntegral f a b (-1 * ((N : ℝ) + 1)) - HIntegral f a b (1 * ((N : ℝ) + 1)) +
        I * (∫ y in -((N : ℝ) + 1)..((N : ℝ) + 1), f ((b : ℂ) + (y : ℂ) * I)) -
        I * (∫ y in -((N : ℝ) + 1)..((N : ℝ) + 1), f ((a : ℂ) + (y : ℂ) * I)) = 0 := by
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      ((a : ℂ) - (((N : ℝ) + 1 : ℝ) : ℂ) * I)
      ((b : ℂ) + (((N : ℝ) + 1 : ℝ) : ℂ) * I) (fun z hz => (hf z ?_).differentiableWithinAt)
    · simpa [HIntegral, smul_eq_mul] using h
    · simpa using (Complex.mem_reProdIm.mp hz).1
  have hh := tendsto_nhds_unique hlim (show Tendsto _ atTop (𝓝 (0 : ℂ)) by
    have he : (fun N : ℕ =>
        HIntegral f a b (-1 * ((N : ℝ) + 1)) - HIntegral f a b (1 * ((N : ℝ) + 1)) +
        I * (∫ y in -((N : ℝ) + 1)..((N : ℝ) + 1), f ((b : ℂ) + (y : ℂ) * I)) -
        I * (∫ y in -((N : ℝ) + 1)..((N : ℝ) + 1), f ((a : ℂ) + (y : ℂ) * I))) =
        fun _ => (0 : ℂ) := funext hzero
    simpa only [Function.comp_def, he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0)))
  simp only [sub_zero, add_zero, zero_add, sub_eq_zero] at hh
  exact (mul_left_cancel₀ I_ne_zero hh).symm

end ZudilinZeta
end
end


-- Source module: missions.zudilin.Params13PhysicalContourIntegral
section
set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology MeasureTheory

namespace ZudilinZeta

lemma params13_physical_integral_shift (n : ℕ) (hn : 2 ≤ n) (a b : ℝ)
    (ha : 87 * (n : ℝ) ≤ a ∧ a ≤ (175 / 2) * n)
    (hb : 87 * (n : ℝ) ≤ b ∧ b ≤ (175 / 2) * n) :
    (∫ y : ℝ, params13PhysicalCos n ((a : ℂ) + (y : ℂ) * I)) =
      ∫ y : ℝ, params13PhysicalCos n ((b : ℂ) + (y : ℂ) * I) := by
  obtain ⟨C, hC, hbound⟩ := params13_physicalCos_envelope n hn
  apply vertical_integral_eq_of_strip _ a b C _
    (integrable_params13PhysicalCos_vertical n hn a ha)
    (integrable_params13PhysicalCos_vertical n hn b hb) hbound
  intro z hz
  apply differentiableAt_params13PhysicalCos n hn
  rcases Set.mem_uIcc.mp hz with h | h <;> constructor <;> linarith

lemma params13_physical_contour_integral (n : ℕ) (hn : 2 ≤ n) (x : ℝ)
    (hx : 87 * (n : ℝ) ≤ x ∧ x ≤ (175 / 2) * n) :
    (-1 : ℂ) ^ (n + 1) *
      (∫ y : ℝ, params13PhysicalCos n ((x : ℂ) + (y : ℂ) * I)) =
        (2 * Real.pi : ℂ) * (F params13 n : ℂ) := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 87 * (n : ℝ) ≤ 87 * n + 1 / 2 ∧ 87 * (n : ℝ) + 1 / 2 ≤ (175 / 2) * n := by
    constructor <;> linarith
  rw [← params13_physical_integral_shift n hn (87 * n + 1 / 2) x hl hx]
  have he : (fun y : ℝ => params13ContourIntegrand n (87 * (n : ℂ) + 1 / 2 + (y : ℂ) * I))
      =ᵐ[volume] (fun y : ℝ => (-1 : ℂ) ^ (n + 1) *
        params13PhysicalCos n (87 * (n : ℂ) + 1 / 2 + (y : ℂ) * I)) := by
    filter_upwards [volume.ae_ne (0 : ℝ)] with y hy
    exact params13_contour_eq_physicalCos n (by omega) _ (by simpa using hy)
  have h := params13_cubic_contour_integral n (by omega)
  rw [integral_congr_ae he, MeasureTheory.integral_const_mul] at h
  simpa using h

end ZudilinZeta
end
end


-- Source module: missions.zudilin.Params13SignedKernelIntegrable
section
set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology MeasureTheory

namespace ZudilinZeta

def params13PhysicalSigned (n : ℕ) (σ : ℝ) (s : ℂ) : ℂ :=
  params13GammaKernel n (s / (n : ℂ)) * Complex.exp ((σ : ℂ) * Real.pi * I * s)

lemma exp_abs_im_le_four_norm_cos (z : ℂ) (hz : 1 ≤ |z.im|) :
    Real.exp |z.im| ≤ 4 * ‖Complex.cos z‖ := by
  have hnorm : Real.sinh |z.im| ≤ ‖Complex.cos z‖ := by
    rw [← Real.abs_sinh]
    have h := norm_cos_sq z
    nlinarith [sq_nonneg (Real.cos z.re), norm_nonneg (Complex.cos z), sq_abs (Real.sinh z.im)]
  have he : 2 ≤ Real.exp |z.im| := by
    have h := Real.add_one_le_exp |z.im|
    linarith
  have hn : Real.exp (-|z.im|) ≤ 1 := by
    simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr (abs_nonneg z.im))
  have hsh := Real.sinh_eq |z.im|
  linarith

lemma norm_exp_pi_le_four_cos (σ : ℝ) (hσ : |σ| ≤ 1) (s : ℂ) (hs : 1 ≤ |s.im|) :
    ‖Complex.exp ((σ : ℂ) * Real.pi * I * s)‖ ≤ 4 * ‖Complex.cos (Real.pi * s)‖ := by
  have hprod : -(σ * s.im) ≤ |s.im| := by
    calc
      _ ≤ |σ * s.im| := neg_le_abs _
      _ = |σ| * |s.im| := abs_mul _ _
      _ ≤ 1 * |s.im| := mul_le_mul_of_nonneg_right hσ (abs_nonneg _)
      _ = _ := one_mul _
  have he : ‖Complex.exp ((σ : ℂ) * Real.pi * I * s)‖ ≤ Real.exp |((Real.pi : ℂ) * s).im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero,
      zero_mul, mul_one, sub_zero, zero_sub, zero_add, add_zero, abs_mul,
      abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  apply he.trans
  apply exp_abs_im_le_four_norm_cos
  simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, abs_mul,
    abs_of_pos Real.pi_pos]
  nlinarith [Real.pi_gt_three]

lemma continuous_params13PhysicalSigned_vertical (n : ℕ) (hn : 2 ≤ n) (σ x : ℝ)
    (hx : 87 * (n : ℝ) ≤ x ∧ x ≤ (175 / 2) * n) :
    Continuous (fun y : ℝ => params13PhysicalSigned n σ ((x : ℂ) + (y : ℂ) * I)) := by
  unfold params13PhysicalSigned
  apply Continuous.mul
  · apply continuous_iff_continuousAt.mpr
    intro y
    have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hsn : 87 ≤ (((x : ℂ) + (y : ℂ) * I) / (n : ℂ)).re ∧
        (((x : ℂ) + (y : ℂ) * I) / (n : ℂ)).re ≤ 175 / 2 := by
      simp only [Complex.div_natCast_re, add_re, ofReal_re, mul_re, ofReal_im,
        I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]
      exact ⟨(le_div_iff₀ hnp).mpr hx.1, (div_le_iff₀ hnp).mpr hx.2⟩
    have hp : ContinuousAt (fun t : ℝ => ((x : ℂ) + (t : ℂ) * I) / (n : ℂ)) y := by fun_prop
    exact (differentiableAt_params13GammaKernel n hn hsn).continuousAt.comp (x := y) hp
  · fun_prop

lemma integrable_params13PhysicalSigned_vertical (n : ℕ) (hn : 2 ≤ n) (σ x : ℝ)
    (hσ : |σ| ≤ 1) (hx : 87 * (n : ℝ) ≤ x ∧ x ≤ (175 / 2) * n) :
    Integrable (fun y : ℝ => params13PhysicalSigned n σ ((x : ℂ) + (y : ℂ) * I)) := by
  obtain ⟨C, hC, hbound⟩ := params13_physicalCos_envelope n hn
  apply integrable_of_continuous_cotEnvelope_tail
    (continuous_params13PhysicalSigned_vertical n hn σ x hx) (4 * C)
  intro y hy
  have hs : 1 ≤ |((x : ℂ) + (y : ℂ) * I).im| := by simpa using hy
  have he := norm_exp_pi_le_four_cos σ hσ ((x : ℂ) + (y : ℂ) * I) hs
  calc
    _ ≤ 4 * ‖params13PhysicalCos n ((x : ℂ) + (y : ℂ) * I)‖ := by
      rw [params13PhysicalSigned, params13PhysicalCos, norm_mul, norm_mul]
      nlinarith [mul_le_mul_of_nonneg_left he
        (norm_nonneg (params13GammaKernel n (((x : ℂ) + (y : ℂ) * I) / (n : ℂ))))]
    _ ≤ 4 * (C * cotEnvelope y) := by
      gcongr
      simpa using hbound ((x : ℂ) + (y : ℂ) * I) hs
    _ = (4 * C) * cotEnvelope y := by ring

lemma integrable_params13_signed_kernel_real (n : ℕ) (hn : 2 ≤ n) (σ x : ℝ)
    (hσ : |σ| ≤ 1) (hx : 87 ≤ x ∧ x ≤ 175 / 2) :
    Integrable (fun y : ℝ => params13GammaKernel n ((x : ℂ) + (y : ℂ) * I) *
      Complex.exp ((σ : ℂ) * (n : ℂ) * Real.pi * I * ((x : ℂ) + (y : ℂ) * I))) := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hnp.ne'
  have h := (integrable_params13PhysicalSigned_vertical n hn σ ((n : ℝ) * x) hσ
    (by constructor <;> nlinarith [hx.1, hx.2])).comp_mul_left' hnp.ne'
  convert! h using 1
  funext y
  simp only [params13PhysicalSigned, ofReal_mul, ofReal_natCast]
  congr 1
  · congr 1
    field_simp
  · congr 1
    ring

end ZudilinZeta
end
end


-- Source module: missions.zudilin.KernelContourSymmetry
section
set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace ZudilinZeta

lemma params13GammaBase_conj (z : ℂ) (i : ℕ) :
    params13GammaBase (starRingEnd ℂ z) i = starRingEnd ℂ (params13GammaBase z i) := by
  simp [params13GammaBase]

lemma params13GammaKernel_conj (n : ℕ) (z : ℂ) :
    params13GammaKernel n (starRingEnd ℂ z) = starRingEnd ℂ (params13GammaKernel n z) := by
  simp only [params13GammaKernel, map_mul, map_sub, map_add, map_ofNat, map_natCast,
    map_prod, map_zpow₀, params13GammaBase_conj]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  rw [← Complex.Gamma_conj]
  simp

lemma integral_vertical_eq_real_part (g : ℂ → ℂ) (τ : ℂ) :
    (∫ t : ℝ, g (τ + (t : ℂ) * I)) =
      ∫ t : ℝ, g ((τ.re : ℂ) + (t : ℂ) * I) := by
  have he (t : ℝ) : τ + (t : ℂ) * I =
      (τ.re : ℂ) + ((t + τ.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp <;> ring
  simp_rw [he]
  exact integral_add_right_eq_self (fun t : ℝ => g ((τ.re : ℂ) + (t : ℂ) * I)) τ.im

lemma params13KernelIntegral_eq_re (n : ℕ) (τ : ℂ) :
    params13KernelIntegral n τ = params13KernelIntegral n (τ.re : ℂ) := by
  exact integral_vertical_eq_real_part
    (fun z => params13GammaKernel n z * Complex.exp (-(n : ℂ) * (Real.pi : ℂ) * I * z)) τ

lemma params13_kernel_plus_integral (n : ℕ) (τ : ℂ) :
    (∫ t : ℝ, params13GammaKernel n (τ + (t : ℂ) * I) *
      Complex.exp ((n : ℂ) * (Real.pi : ℂ) * I * (τ + (t : ℂ) * I))) =
      starRingEnd ℂ (params13KernelIntegral n τ) := by
  rw [params13KernelIntegral_eq_re, params13KernelIntegral, ← integral_conj]
  rw [integral_vertical_eq_real_part
    (fun z => params13GammaKernel n z * Complex.exp ((n : ℂ) * (Real.pi : ℂ) * I * z)) τ]
  rw [← integral_neg_eq_self (fun t : ℝ =>
    params13GammaKernel n ((τ.re : ℂ) + (t : ℂ) * I) *
      Complex.exp ((n : ℂ) * (Real.pi : ℂ) * I * ((τ.re : ℂ) + (t : ℂ) * I))) volume]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [map_mul, ← Complex.exp_conj, ← params13GammaKernel_conj,
    map_add, Complex.conj_ofReal, Complex.conj_I, map_neg, map_natCast,
    Complex.ofReal_neg]
  congr 1 <;> congr 1 <;> ring

lemma params13_kernel_cos_integral (n : ℕ) (τ : ℂ)
    (hm : Integrable (fun t : ℝ => params13GammaKernel n (τ + (t : ℂ) * I) *
      Complex.exp (-(n : ℂ) * (Real.pi : ℂ) * I * (τ + (t : ℂ) * I))))
    (hp : Integrable (fun t : ℝ => params13GammaKernel n (τ + (t : ℂ) * I) *
      Complex.exp ((n : ℂ) * (Real.pi : ℂ) * I * (τ + (t : ℂ) * I)))) :
    (∫ t : ℝ, params13GammaKernel n (τ + (t : ℂ) * I) *
      Complex.cos ((n : ℂ) * (Real.pi : ℂ) * (τ + (t : ℂ) * I))) =
      ((params13KernelIntegral n τ).re : ℂ) := by
  have he (t : ℝ) :
      params13GammaKernel n (τ + (t : ℂ) * I) *
        Complex.cos ((n : ℂ) * (Real.pi : ℂ) * (τ + (t : ℂ) * I)) =
      (params13GammaKernel n (τ + (t : ℂ) * I) *
        Complex.exp (-(n : ℂ) * (Real.pi : ℂ) * I * (τ + (t : ℂ) * I)) +
      params13GammaKernel n (τ + (t : ℂ) * I) *
        Complex.exp ((n : ℂ) * (Real.pi : ℂ) * I * (τ + (t : ℂ) * I))) / 2 := by
    have htwo := Complex.two_cos ((n : ℂ) * (Real.pi : ℂ) * (τ + (t : ℂ) * I))
    have ep : (n : ℂ) * (Real.pi : ℂ) * (τ + (t : ℂ) * I) * I =
        (n : ℂ) * (Real.pi : ℂ) * I * (τ + (t : ℂ) * I) := by ring
    have em : -((n : ℂ) * (Real.pi : ℂ) * (τ + (t : ℂ) * I)) * I =
        -(n : ℂ) * (Real.pi : ℂ) * I * (τ + (t : ℂ) * I) := by ring
    rw [ep, em] at htwo
    linear_combination (params13GammaKernel n (τ + (t : ℂ) * I) / 2) * htwo
  rw [integral_congr_ae (ae_of_all _ he), integral_div, integral_add hm hp,
    params13_kernel_plus_integral]
  change (params13KernelIntegral n τ + starRingEnd ℂ (params13KernelIntegral n τ)) / 2 = _
  apply Complex.ext <;> simp

end ZudilinZeta
end
end


-- Source module: missions.zudilin.Params13ContourFormula
section
set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology MeasureTheory

namespace ZudilinZeta

lemma params13_physical_cos_integral_scale (n : ℕ) (hn : 0 < n) (x : ℝ) :
    (∫ y : ℝ, params13PhysicalCos n (((n : ℝ) * x : ℝ) + (y : ℂ) * I)) =
      (n : ℂ) * ∫ y : ℝ, params13GammaKernel n ((x : ℂ) + (y : ℂ) * I) *
        Complex.cos ((n : ℂ) * Real.pi * ((x : ℂ) + (y : ℂ) * I)) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := Measure.integral_comp_mul_left
    (fun y : ℝ => params13PhysicalCos n (((n : ℝ) * x : ℝ) + (y : ℂ) * I)) (n : ℝ)
  have he (y : ℝ) :
      params13PhysicalCos n (((n : ℝ) * x : ℝ) + (((n : ℝ) * y : ℝ) : ℂ) * I) =
        params13GammaKernel n ((x : ℂ) + (y : ℂ) * I) *
          Complex.cos ((n : ℂ) * Real.pi * ((x : ℂ) + (y : ℂ) * I)) := by
    simp only [params13PhysicalCos, ofReal_mul, ofReal_natCast]
    congr 1
    · congr 1
      field_simp
    · congr 1
      ring
  simp_rw [he] at h
  rw [abs_of_pos (inv_pos.mpr hnR), Complex.real_smul, ofReal_inv, ofReal_natCast] at h
  rw [h, ← mul_assoc, mul_inv_cancel₀ hnC, one_mul]

lemma params13_signed_contour_formula_real (n : ℕ) (hn : 2 ≤ n) (x : ℝ)
    (hx : 87 ≤ x ∧ x ≤ 175 / 2) :
    (-1 : ℂ) ^ (n + 1) * (n : ℂ) * ((params13KernelIntegral n (x : ℂ)).re : ℂ) =
      (2 * Real.pi : ℂ) * (F params13 n : ℂ) := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := params13_physical_contour_integral n hn ((n : ℝ) * x)
    (by constructor <;> nlinarith [hx.1, hx.2])
  rw [params13_physical_cos_integral_scale n (by omega) x] at h
  have hm : Integrable (fun y : ℝ => params13GammaKernel n ((x : ℂ) + (y : ℂ) * I) *
      Complex.exp (-(n : ℂ) * Real.pi * I * ((x : ℂ) + (y : ℂ) * I))) := by
    simpa only [ofReal_neg, ofReal_one, neg_one_mul] using
      integrable_params13_signed_kernel_real n hn (-1) x (by norm_num) hx
  have hp : Integrable (fun y : ℝ => params13GammaKernel n ((x : ℂ) + (y : ℂ) * I) *
      Complex.exp ((n : ℂ) * Real.pi * I * ((x : ℂ) + (y : ℂ) * I))) := by
    simpa only [ofReal_one, one_mul] using
      integrable_params13_signed_kernel_real n hn 1 x (by norm_num) hx
  rw [params13_kernel_cos_integral n (x : ℂ) hm hp] at h
  simpa only [mul_assoc] using h

lemma params13_contour_formula_real (n : ℕ) (hn : 2 ≤ n) (x : ℝ)
    (hx : 87 ≤ x ∧ x ≤ 175 / 2) :
    |F params13 n| = (n : ℝ) / (2 * Real.pi) * |(params13KernelIntegral n (x : ℂ)).re| := by
  have h := congrArg norm (params13_signed_contour_formula_real n hn x hx)
  have hp : (0 : ℝ) < 2 * Real.pi := by positivity
  have he : (n : ℝ) * |(params13KernelIntegral n (x : ℂ)).re| =
      (2 * Real.pi) * |F params13 n| := by
    simpa only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
      norm_ofNat, abs_of_pos Real.pi_pos] using h
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hp.ne').mpr
  linarith

theorem params13_contour_formula_proved
    (τ : ℂ) (hτ : 87 ≤ τ.re ∧ τ.re ≤ 175 / 2) (n : ℕ) (hn : 2 ≤ n) :
    |F params13 n| = (n : ℝ) / (2 * Real.pi) * |(params13KernelIntegral n τ).re| := by
  rw [params13KernelIntegral_eq_re]
  exact params13_contour_formula_real n hn τ.re hτ

end ZudilinZeta
end
end


theorem solution
    (τ : ℂ) (hτ : 87 ≤ τ.re ∧ τ.re ≤ 175 / 2) (n : ℕ) (hn : 2 ≤ n) :
    |ZudilinZeta.F ZudilinZeta.params13 n| = (n : ℝ) / (2 * Real.pi) *
      |(ZudilinZeta.params13KernelIntegral n τ).re| := by
  exact ZudilinZeta.params13_contour_formula_proved τ hτ n hn
