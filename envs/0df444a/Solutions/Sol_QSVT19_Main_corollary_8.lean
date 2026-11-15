-- Prove2me | solution 1 for QSVT19.Main.corollary_8
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T22:20:19.292807+00:00
-- url     : https://prove2.me/submissions/5a0b73bc-db8f-4a74-a219-2a5ec9df0a50

import Definitions.Def_QSVT19_Main_Setting
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Theorems.Thm_QAlgorithms_Childs_qsp_characterization
import Theorems.Thm_QSVT19_Main_theorem_4_first_claim

noncomputable section
open Polynomial QAlgorithms QSVT19.Main
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QSVTRefl
lemma Z_add (a b : ℝ) : qspZ (a+b) = qspZ a * qspZ b := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [qspZ,Matrix.mul_apply,Fin.sum_univ_two,Complex.ofReal_add,add_mul,neg_add,Complex.exp_add] <;> ring
lemma Z_zero : qspZ 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [qspZ]
lemma Z_sub (a b : ℝ) : qspZ (a-b) = qspZ a * qspZ (-b) := by
  simpa [sub_eq_add_neg] using Z_add a (-b)
lemma W_convert (x : ℝ) : qspW x = Complex.I • (qspZ (-Real.pi/4)*reflR x*qspZ (-Real.pi/4)) := by
  have hp : Complex.exp (((Real.pi/4:ℝ):ℂ)*Complex.I)^2 = Complex.I := by
    rw [← Complex.exp_nat_mul]
    convert Complex.exp_pi_div_two_mul_I using 1 <;> congr 1 <;> push_cast <;> ring
  have hn : Complex.exp (-(((Real.pi/4:ℝ):ℂ)*Complex.I))^2 = -Complex.I := by
    rw [← Complex.exp_nat_mul]
    convert Complex.exp_neg_pi_div_two_mul_I using 1 <;> congr 1 <;> push_cast <;> ring
  have hm : Complex.exp (((Real.pi/4:ℝ):ℂ)*Complex.I)*Complex.exp (-(((Real.pi/4:ℝ):ℂ)*Complex.I))=1 := by
    rw [← Complex.exp_add];simp
  have hp' : -Complex.I*Complex.exp (((Real.pi/4:ℝ):ℂ)*Complex.I)^2=1 := by rw [hp]; simp [Complex.I_sq]
  have hn' : Complex.I*Complex.exp (-(((Real.pi/4:ℝ):ℂ)*Complex.I))^2=1 := by rw [hn]; simp [Complex.I_sq]
  simp only [Complex.ofReal_div,Complex.ofReal_ofNat] at hp' hn' hm
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [qspW,qspZ,reflR,Matrix.smul_apply,Matrix.mul_apply,Fin.sum_univ_two] <;>
    simp only [neg_div,neg_mul,neg_neg]
  · linear_combination -(x:ℂ)*hn'
  · linear_combination -(Real.sqrt (1-x^2):ℂ)*hm
  · linear_combination -(Real.sqrt (1-x^2):ℂ)*hm
  · linear_combination -(x:ℂ)*hp'
lemma refl_last {n : ℕ} (Φ : Fin (n+1) → ℝ) (x : ℝ) :
    qspRefl Φ x = qspRefl (fun i : Fin n => Φ i.castSucc) x *
      (qspZ (Φ (Fin.last n))*reflR x) := by
  unfold qspRefl
  rw [List.ofFn_succ',List.prod_concat]
lemma refl_cons {n : ℕ} (Φ : Fin (n+1) → ℝ) (x : ℝ) :
    qspRefl Φ x = (qspZ (Φ 0)*reflR x) * qspRefl (fun i : Fin n => Φ i.succ) x := by
  simp [qspRefl,List.ofFn_succ]
lemma refl_empty (Φ : Fin 0 → ℝ) (x : ℝ) : qspRefl Φ x = 1 := by simp [qspRefl]
lemma sequence_last {k : ℕ} (Φ : Fin (k+2) → ℝ) (x : ℝ) :
    qspSequence Φ x = qspSequence (fun i : Fin (k+1) => Φ i.castSucc) x *
      (qspW x * qspZ (Φ (Fin.last (k+1)))) := by
  unfold qspSequence
  rw [List.ofFn_succ',List.prod_concat]
  simp only [show (Fin.last (k+1) : Fin (k+2)) ≠ 0 by
    intro h;have := congrArg Fin.val h;simp at this,if_false]
  congr 1
  congr 1
  congr 1
  funext i
  simp only [Fin.ext_iff,Fin.val_castSucc,Fin.val_zero]
lemma sequence_reflections : ∀ n : ℕ, ∀ Φ : Fin (n+1) → ℝ,
    ∃ Ψ : Fin n → ℝ, ∃ β : ℝ, ∀ x : ℝ,
      qspSequence Φ x = Complex.I^n • (qspRefl Ψ x * qspZ β) := by
  intro n
  induction n with
  | zero =>
    intro Φ
    exact ⟨Fin.elim0,Φ 0,by intro x;simp [qspSequence,qspRefl]⟩
  | succ n ih =>
    intro Φ
    obtain ⟨Ψ,β,h⟩ := ih (fun i => Φ i.castSucc)
    refine ⟨Fin.lastCases (β-Real.pi/4) Ψ, Φ (Fin.last (n+1))-Real.pi/4,?_⟩
    intro x
    rw [sequence_last,h,W_convert,refl_last]
    simp only [Fin.lastCases_castSucc,Fin.lastCases_last,Matrix.smul_mul,Matrix.mul_smul,
      smul_smul,pow_succ]
    rw [mul_comm Complex.I (Complex.I^n)]
    congr 1
    simp only [Z_sub,mul_assoc]
    rw [← Z_add (-Real.pi/4) (Φ (Fin.last (n+1)))]
    rw [← Z_add (Φ (Fin.last (n+1))) (-(Real.pi/4))]
    congr 3 <;> ring
lemma shift_first {n : ℕ} (Ψ : Fin (n+1) → ℝ) (a x : ℝ) :
    qspRefl (fun i => if i=0 then a+Ψ i else Ψ i) x = qspZ a * qspRefl Ψ x := by
  rw [refl_cons,refl_cons]
  simp only [ite_true]
  rw [Z_add]
  simp only [ite_true,show ∀ i : Fin n, (i.succ : Fin (n+1)) ≠ 0 by intro i;exact Fin.succ_ne_zero i,ite_false]
  simp only [mul_assoc]
lemma convert_top_left (n : ℕ) (hn : 1 ≤ n) (Φ : Fin (n+1) → ℝ) :
    ∃ Ψ : Fin n → ℝ, ∀ x : ℝ, qspRefl Ψ x 0 0 = qspSequence Φ x 0 0 := by
  obtain ⟨Ψ,β,h⟩ := sequence_reflections n Φ
  have he : Complex.exp (((n:ℝ)*Real.pi/2+β:ℝ)*Complex.I) = Complex.I^n * Complex.exp ((β:ℂ)*Complex.I) := by
    rw [show (((n:ℝ)*Real.pi/2+β:ℝ):ℂ)*Complex.I = (n:ℂ)*(Real.pi/2*Complex.I)+(β:ℂ)*Complex.I by push_cast;ring,
      Complex.exp_add,Complex.exp_nat_mul,Complex.exp_pi_div_two_mul_I]
  cases n with
  | zero => omega
  | succ n =>
    refine ⟨fun i => if i=0 then ((n+1:ℕ):ℝ)*Real.pi/2+β+Ψ i else Ψ i,?_⟩
    intro x
    rw [shift_first,h]
    simp only [Matrix.smul_apply,smul_eq_mul,Matrix.mul_apply,Fin.sum_univ_two,qspZ,
      Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
      zero_mul,mul_zero,add_zero]
    rw [he]
    ring
end QSVTRefl

noncomputable section
open Polynomial QAlgorithms QSVT19.Main
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QSVTRefl
lemma boundary (n : ℕ) (Φ : Fin n → ℝ) (x : ℝ) (hx : x=-1 ∨ x=1) :
    qspRefl Φ x 0 0 = (x:ℂ)^n * ∏ j : Fin n, Complex.exp ((Φ j:ℂ)*Complex.I) := by
  have hs : Real.sqrt (1-x^2)=0 := by rcases hx with rfl|rfl <;> norm_num
  induction n with
  | zero => simp [qspRefl]
  | succ n ih =>
    rw [refl_cons]
    have hh := ih (fun i => Φ i.succ)
    simp only [Matrix.mul_apply,Fin.sum_univ_two,qspZ,reflR,hs,
      Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
      Complex.ofReal_zero,mul_zero,zero_mul,add_zero,zero_add]
    rw [hh,Fin.prod_univ_succ,pow_succ]
    ring
lemma R_zero_square : reflR 0 * reflR 0 = 1 := by
  ext i j;fin_cases i <;>fin_cases j <;>simp [reflR,Matrix.mul_apply,Fin.sum_univ_two]
lemma R_zero_phase (a : ℝ) : reflR 0 * qspZ a = qspZ (-a) * reflR 0 := by
  ext i j;fin_cases i <;>fin_cases j <;>
    simp [qspZ,reflR,Matrix.mul_apply,Fin.sum_univ_two]
lemma zero_product (n : ℕ) (Φ : Fin n → ℝ) :
    qspRefl Φ 0 = qspZ (∑ j : Fin n, (-1:ℝ)^j.val*Φ j) * reflR 0 ^ n := by
  induction n with
  | zero => simp [qspRefl,Z_zero]
  | succ n ih =>
    rw [refl_cons,ih]
    simp only [mul_assoc]
    rw [← mul_assoc (reflR 0),R_zero_phase]
    simp only [mul_assoc]
    rw [← mul_assoc (qspZ (Φ 0)) (qspZ (-(∑ j : Fin n, (-1:ℝ)^j.val*Φ j.succ))) (reflR 0 * reflR 0^n),← Z_add,← pow_succ']
    congr 2
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero,pow_zero,one_mul,Fin.val_succ,pow_succ,Finset.sum_neg_distrib,neg_mul,mul_neg,mul_one]
lemma zero_even (n : ℕ) (Φ : Fin n → ℝ) (hn : Even n) :
    qspRefl Φ 0 0 0 = Complex.exp (-(∑ j : Fin n,(-1:ℂ)^(j.val+1)*(Φ j:ℂ))*Complex.I) := by
  have hp : reflR 0 ^ n = 1 := by
    obtain ⟨k,hk⟩ := hn
    rw [hk,← two_mul,pow_mul,pow_two,R_zero_square]
    simp
  rw [zero_product,hp,mul_one]
  simp only [qspZ,Matrix.of_apply,Matrix.cons_val_zero]
  congr 1
  congr 1
  push_cast
  simp only [pow_succ,mul_neg,mul_one,neg_mul,Finset.sum_neg_distrib,neg_neg]
end QSVTRefl

noncomputable section
open Polynomial QAlgorithms QSVT19.Main
open scoped ComplexOrder
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QSVTRefl
lemma cor8_checked (d : ℕ) (hd : 1 ≤ d) (P : ℂ[X]) (hP : Cor8Requirements d P) :
    ∃ Φ : Fin d → ℝ, (∀ x ∈ Set.Icc (-1:ℝ) 1, qspRefl Φ x 0 0 = P.eval (x:ℂ)) ∧
    (∀ x : ℝ, (x=-1 ∨ x=1) → P.eval (x:ℂ) = (x:ℂ)^d*∏ j : Fin d, Complex.exp ((Φ j:ℂ)*Complex.I)) ∧
    (Even d → P.eval 0 = Complex.exp (-(∑ j : Fin d,(-1:ℂ)^(j.val+1)*(Φ j:ℂ))*Complex.I)) := by
  have hdeg : P.degree ≤ d := natDegree_le_iff_degree_le.mp hP.1.le
  obtain ⟨Q,hQ⟩ := (theorem_4_first_claim d P).mpr ⟨⟨hdeg,hP.2.1⟩,hP.2.2⟩
  obtain ⟨Φ,hΦ⟩ := (QAlgorithms.Childs.qsp_characterization d P Q).mpr hQ
  obtain ⟨Ψ,hΨ⟩ := convert_top_left d hd Φ
  have htop : ∀ x ∈ Set.Icc (-1:ℝ) 1, qspRefl Ψ x 0 0 = P.eval (x:ℂ) := by
    intro x hx
    rw [hΨ x,hΦ x hx]
    rfl
  refine ⟨Ψ,htop,?_,?_⟩
  · intro x hx
    have hx' : x ∈ Set.Icc (-1:ℝ) 1 := by rcases hx with rfl|rfl <;> norm_num
    rw [← htop x hx']
    exact boundary d Ψ x hx
  · intro he
    have hh := htop 0 (by norm_num)
    simpa only [Complex.ofReal_zero] using hh.symm.trans (zero_even d Ψ he)
end QSVTRefl

set_option autoImplicit false
open QSVT19.Main


/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Corollary 8, pp. 12–13: "Let P ∈ C[x] be a degree-d polynomial, such that
• P has parity-(d mod 2), • ∀x ∈ [−1, 1]: |P(x)| ≤ 1, • ∀x ∈ (−∞, −1] ∪ [1, ∞): |P(x)| ≥ 1,
• if d is even, then ∀x ∈ R: P(ix)P^∗(ix) ≥ 1.
Then there exists Φ ∈ R^d such that ∏_{j=1}^d (e^{iφ_jσ_z}R(x)) = [P(x) .; . .]. (14)
Moreover for x ∈ {−1, 1} we have that P(x) = x^d ∏_{j=1}^d e^{iφ_j}, and for d even
P(0) = e^{−i∑_{j=1}^d(−1)^jφ_j}."

**Formalization Note.** The four bullets and "degree-d" are `Cor8Requirements d P`. (14) is
required for every `x ∈ [−1, 1]`, the domain of `R(x)` (Definition 7); "`[P(x) .; . .]`" says that
the top-left entry is `P(x)`. The "Moreover" values are stated for the same `Φ`. `Φ` is 0-based, so
the paper's `(−1)^j` (with `j = 1, …, d`) is `(−1)^(j+1)` for `j : Fin d`. The hypothesis `1 ≤ d`
is added: at `d = 0` the statement is false (`P ≡ e^{iα}`, `α ∉ 2πℤ`, meets every bullet, while
the empty product is `I`); the proof says "for some d ≥ 1". -/
theorem solution (d : ℕ) (hd : 1 ≤ d) (P : ℂ[X]) (hP : Cor8Requirements d P) :
    ∃ Φ : Fin d → ℝ, (∀ x ∈ Set.Icc (-1 : ℝ) 1, qspRefl Φ x 0 0 = P.eval (x : ℂ)) ∧ (∀ x : ℝ, (x = -1 ∨ x = 1) → P.eval (x : ℂ) = (x : ℂ) ^ d * ∏ j : Fin d, Complex.exp (Φ j * Complex.I)) ∧ (Even d → P.eval 0 = Complex.exp (-(∑ j : Fin d, (-1 : ℂ) ^ (j.val + 1) * (Φ j : ℂ)) * Complex.I)) := by
  exact QSVTRefl.cor8_checked d hd P hP