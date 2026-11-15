-- Prove2me | solution 1 for QSVT19.Main.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T21:23:26.699321+00:00
-- url     : https://prove2.me/submissions/57c5ba37-0d97-48e2-b4a0-b199422b91cd

import Definitions.Def_QSVT19_Main_Setting
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
noncomputable section
open Polynomial QAlgorithms QSVT19.Main
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QSVTCheb
 def rot (a : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos a:ℂ),(Real.sin a:ℂ);-(Real.sin a:ℂ),(Real.cos a:ℂ)]
lemma rot_add (a b : ℝ) : rot (a+b) = rot a * rot b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot,Matrix.mul_apply,Fin.sum_univ_two,Real.cos_add,Real.sin_add] <;> ring
lemma rot_pow (a : ℝ) (n : ℕ) : rot a^n = rot ((n:ℝ)*a) := by
  induction n with
  | zero => ext i j;fin_cases i <;>fin_cases j <;>simp [rot]
  | succ n ih =>
    rw [pow_succ,ih,← rot_add]
    congr 1
    push_cast
    ring
lemma quarter_reflection (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) :
    qspZ (Real.pi/2) * reflR x = Complex.I • rot (Real.arccos x) := by
  have hc := Real.cos_arccos hx.1 hx.2
  have hs := Real.sin_arccos x
  have hneg : Complex.exp (-(((Real.pi/2:ℝ):ℂ)*Complex.I)) = -Complex.I := by
    convert Complex.exp_neg_pi_div_two_mul_I using 1 <;> congr 1 <;> push_cast <;> ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qspZ,reflR,rot,Matrix.mul_apply,Fin.sum_univ_two,Matrix.smul_apply,
      Complex.exp_pi_div_two_mul_I,Complex.exp_neg,hc,hs] <;> ring
lemma phase_cancel (n : ℕ) :
    Complex.exp ((((1-((n+1:ℕ):ℝ))*Real.pi/2 : ℝ):ℂ)*Complex.I) * Complex.I^n = 1 := by
  have he : ((((1-((n+1:ℕ):ℝ))*Real.pi/2 : ℝ):ℂ)*Complex.I) =
      (n:ℂ)*(-Real.pi/2*Complex.I) := by push_cast;ring
  rw [he,Complex.exp_nat_mul,Complex.exp_neg_pi_div_two_mul_I,← mul_pow]
  simp [Complex.I_sq]
lemma lemma9_checked (d : ℕ) (hd : 1 ≤ d) :
    ∀ x ∈ Set.Icc (-1:ℝ) 1,
      qspRefl (fun j : Fin d => if j.val=0 then (1-(d:ℝ))*Real.pi/2 else Real.pi/2) x 0 0 =
      (((Polynomial.Chebyshev.T ℝ (d:ℤ)).eval x : ℝ):ℂ) := by
  intro x hx
  cases d with
  | zero => omega
  | succ n =>
    have hc := Real.cos_arccos hx.1 hx.2
    have hs := Real.sin_arccos x
    have hseq : qspRefl (fun j : Fin (n+1) => if j.val=0 then (1-((n+1:ℕ):ℝ))*Real.pi/2 else Real.pi/2) x =
        (qspZ ((1-((n+1:ℕ):ℝ))*Real.pi/2)*reflR x) * (qspZ (Real.pi/2)*reflR x)^n := by
      simp [qspRefl,List.ofFn_succ,List.ofFn_const,List.prod_replicate]
    rw [hseq,quarter_reflection x hx,_root_.smul_pow,rot_pow]
    have he := phase_cancel n
    have hcos : (Polynomial.Chebyshev.T ℝ ((n+1:ℕ):ℤ)).eval x =
        Real.cos (((n+1:ℕ):ℝ)*Real.arccos x) := by
      have hh := Polynomial.Chebyshev.T_real_cos (Real.arccos x) ((n+1:ℕ):ℤ)
      rw [hc] at hh
      exact_mod_cast hh
    rw [hcos]
    simp only [Matrix.mul_smul,Matrix.smul_apply,smul_eq_mul,Matrix.mul_apply,Fin.sum_univ_two,
      qspZ,reflR,rot,Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
    have he' : Complex.I^n * Complex.exp ((((1-((n+1:ℕ):ℝ))*Real.pi/2 : ℝ):ℂ)*Complex.I) = 1 := by
      rw [mul_comm];exact he
    have hangle : (((n+1:ℕ):ℝ)*Real.arccos x) = Real.arccos x+(n:ℝ)*Real.arccos x := by push_cast;ring
    rw [hangle,Real.cos_add,hc,hs]
    simp only [Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_div,
      Complex.ofReal_natCast,Complex.ofReal_one,Complex.ofReal_ofNat] at he' ⊢
    linear_combination (x*(Real.cos ((n:ℝ)*Real.arccos x):ℂ)-(Real.sqrt (1-x^2):ℂ)*(Real.sin ((n:ℝ)*Real.arccos x):ℂ))*he'
end QSVTCheb

set_option autoImplicit false
open QSVT19.Main


/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Lemma 9, p. 13: "Let T_d ∈ R[x] be the d-th Chebyshev polynomial of the first kind. Let
Φ ∈ R^d be such that φ_1 = (1 − d)π/2, and for all i ∈ [d] \ {1} let φ_i := π/2. Using this Φ in
equation (14) we get that P = T_d."

**Formalization Note.** "Using this Φ in (14) we get P = T_d" is: the top-left entry of
`∏_{j=1}^d e^{iφ_jσ_z}R(x)` equals `T_d(x)` for every `x ∈ [−1, 1]` (the domain of `R(x)`). The
0-based index `j = 0` is the paper's `φ_1`. `T_d` is Mathlib's `Polynomial.Chebyshev.T ℝ d`
(integer-indexed, at `d : ℕ`), which satisfies `T_d(cos θ) = cos(dθ)` as in §2. `1 ≤ d` because
`φ_1` must exist. -/
theorem solution (d : ℕ) (hd : 1 ≤ d) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, qspRefl (fun j : Fin d => if j.val = 0 then (1 - (d : ℝ)) * Real.pi / 2 else Real.pi / 2) x 0 0 = (((Polynomial.Chebyshev.T ℝ (d : ℤ)).eval x : ℝ) : ℂ) := by
  exact QSVTCheb.lemma9_checked d hd