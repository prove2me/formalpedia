-- Prove2me | solution 1 for TightPQRepetition.Main.theorem_3_9
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T15:49:01.729356+00:00
-- url     : https://prove2.me/submissions/3967fd66-772a-4dc0-830a-051de1b79aa4

import Mathlib
import Definitions.Def_TightPQRepetition_Main_Jordan
import Theorems.Thm_QSVT19_Main_corollary_8

namespace TightPQRepetition.Main

open scoped InnerProductSpace

section Circuit

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- phase operator `e^{-iφ}(1-P) + e^{iφ}P`. -/
noncomputable def Fop (P : A) (φ : ℝ) : A :=
  algebraMap ℂ A (Complex.exp (-(φ : ℂ) * Complex.I)) * (1 - P) +
    algebraMap ℂ A (Complex.exp ((φ : ℂ) * Complex.I)) * P

/-- one phase layer: `C_P NOT · diag(e^{-iφ}, e^{iφ}) · C_P NOT`. -/
noncomputable def pairProg (isA : Bool) (φ : ℝ) : RotationProgram :=
  let c := if isA then RotationInstr.callA else RotationInstr.callB
  [c, .gate !![Complex.exp (-(φ : ℂ) * Complex.I), 0; 0, Complex.exp ((φ : ℂ) * Complex.I)], c]

noncomputable def progOf (l : List (Bool × ℝ)) : RotationProgram :=
  l.flatMap fun x => pairProg x.1 x.2

/-- the operator on ancilla `|0⟩` (sign `s = 1`) / `|1⟩` (sign `s = -1`). -/
noncomputable def Uop (PA PB : A) (s : ℝ) : List (Bool × ℝ) → A
  | [] => 1
  | x :: l => Uop PA PB s l * Fop (if x.1 then PA else PB) (s * x.2)

lemma cnot_op (P : A) (hP : P * P = P) (a b : ℂ) :
    cNot P * (!![a, 0; 0, b].map (algebraMap ℂ A)) * cNot P =
      !![algebraMap ℂ A a * (1 - P) + algebraMap ℂ A b * P, 0;
         0, algebraMap ℂ A a * P + algebraMap ℂ A b * (1 - P)] := by
  have h1 : (1 - P) * P = 0 := by rw [sub_mul, hP]; simp
  have h2 : P * (1 - P) = 0 := by rw [mul_sub, hP]; simp
  have h3 : (1 - P) * (1 - P) = 1 - P := by
    have e : (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
    rw [e, hP]; abel
  have c1 : ∀ z : ℂ, Commute (algebraMap ℂ A z) P := fun z => Algebra.commutes z P
  have g : (!![a, 0; 0, b].map (algebraMap ℂ A) : Matrix (Fin 2) (Fin 2) A)
      = !![algebraMap ℂ A a, 0; 0, algebraMap ℂ A b] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [g]
  simp only [cNot, Matrix.mul_fin_two]
  have k : ∀ z : ℂ, (1 - P) * algebraMap ℂ A z = algebraMap ℂ A z * (1 - P) := fun z => by
    rw [mul_sub, sub_mul, mul_one, one_mul, ← (c1 z).eq]
  have k2 : ∀ z : ℂ, P * algebraMap ℂ A z = algebraMap ℂ A z * P := fun z => (c1 z).eq.symm
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · rw [k, mul_assoc, h3, k2, mul_assoc, hP]
  · rw [k, mul_assoc, h1, mul_zero, k2, mul_assoc, h2, mul_zero, zero_add]
  · rw [k2, mul_assoc, h2, mul_zero, k, mul_assoc, h1, mul_zero, zero_add]
  · rw [k2, mul_assoc, hP, k, mul_assoc, h3]

lemma comb_mul (P : A) (hP : P * P = P) (u v u' v' : ℂ) :
    (algebraMap ℂ A u * (1 - P) + algebraMap ℂ A v * P) *
      (algebraMap ℂ A u' * (1 - P) + algebraMap ℂ A v' * P) =
    algebraMap ℂ A (u * u') * (1 - P) + algebraMap ℂ A (v * v') * P := by
  have h1 : (1 - P) * P = 0 := by rw [sub_mul, hP]; simp
  have h2 : P * (1 - P) = 0 := by rw [mul_sub, hP]; simp
  have h3 : (1 - P) * (1 - P) = 1 - P := by
    have e : (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
    rw [e, hP]; abel
  have tt : ∀ (x y : ℂ) (Q R : A), Commute (algebraMap ℂ A y) Q →
      algebraMap ℂ A x * Q * (algebraMap ℂ A y * R) = algebraMap ℂ A (x * y) * (Q * R) := by
    intro x y Q R hc
    rw [map_mul, mul_assoc, ← mul_assoc Q, ← hc.eq, mul_assoc, mul_assoc]
  have cP : ∀ z : ℂ, Commute (algebraMap ℂ A z) P := fun z => Algebra.commutes z P
  have cQ : ∀ z : ℂ, Commute (algebraMap ℂ A z) (1 - P) := fun z => (Commute.one_right (algebraMap ℂ A z)).sub_right (cP z)
  rw [mul_add, add_mul, add_mul, tt _ _ _ _ (cQ _), tt _ _ _ _ (cP _), tt _ _ _ _ (cQ _),
    tt _ _ _ _ (cP _), h3, h1, h2, hP, mul_zero, mul_zero]
  simp

lemma Fop_mul (P : A) (hP : P * P = P) (φ ψ : ℝ) : Fop P φ * Fop P ψ = Fop P (φ + ψ) := by
  simp only [Fop]
  rw [comb_mul P hP, ← Complex.exp_add, ← Complex.exp_add]
  congr 3 <;> push_cast <;> ring_nf

lemma Fop_zero (P : A) : Fop P 0 = 1 := by
  simp [Fop]

lemma Fop_unitary [StarRing A] [StarModule ℂ A] (P : A) (hP : P * P = P) (hs : IsSelfAdjoint P)
    (φ : ℝ) : Fop P φ ∈ unitary A := by
  have hstar : star (Fop P φ) = Fop P (-φ) := by
    have c1 : ∀ z : ℂ, Commute (algebraMap ℂ A z) P := fun z => Algebra.commutes z P
    have cQ : ∀ z : ℂ, Commute (algebraMap ℂ A z) (1 - P) := fun z =>
      (Commute.one_right (algebraMap ℂ A z)).sub_right (c1 z)
    simp only [Fop, star_add, star_mul, star_sub, star_one, hs.star_eq]
    rw [← algebraMap_star_comm, ← algebraMap_star_comm, ← (cQ _).eq, ← (c1 _).eq]
    have e1 : star (Complex.exp (-(φ : ℂ) * Complex.I)) = Complex.exp (-((-φ : ℝ) : ℂ) * Complex.I) := by
      show (starRingEnd ℂ) _ = _
      rw [← Complex.exp_conj]; congr 1; simp
    have e2 : star (Complex.exp ((φ : ℂ) * Complex.I)) = Complex.exp (((-φ : ℝ) : ℂ) * Complex.I) := by
      show (starRingEnd ℂ) _ = _
      rw [← Complex.exp_conj]; congr 1; simp
    rw [e1, e2, add_comm]
  rw [Unitary.mem_iff, hstar, Fop_mul P hP, Fop_mul P hP]
  simp [Fop_zero]

lemma pair_op (PA PB : A) (hA : PA * PA = PA) (hB : PB * PB = PB) (b : Bool) (φ : ℝ) :
    programOp PA PB (pairProg b φ) =
      !![Fop (if b then PA else PB) φ, 0; 0, Fop (if b then PA else PB) (-φ)] := by
  have key : ∀ P : A, P * P = P → (if b then PA else PB) = P →
      programOp PA PB (pairProg b φ) = !![Fop P φ, 0; 0, Fop P (-φ)] := by
    intro P hP hb
    cases b <;> simp at hb <;> subst hb <;>
    · simp only [programOp, pairProg, instrOp, Bool.false_eq_true, if_false, if_true,
        List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append, List.prod_cons, List.prod_nil, mul_one]
      rw [← mul_assoc, cnot_op _ hP]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Fop, add_comm]
  cases b
  · exact key PB hB rfl
  · exact key PA hA rfl

lemma programOp_append (PA PB : A) (p q : RotationProgram) :
    programOp PA PB (p ++ q) = programOp PA PB q * programOp PA PB p := by
  simp [programOp]

lemma prog_op (PA PB : A) (hA : PA * PA = PA) (hB : PB * PB = PB) (l : List (Bool × ℝ)) :
    programOp PA PB (progOf l) = !![Uop PA PB 1 l, 0; 0, Uop PA PB (-1) l] := by
  induction l with
  | nil =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp [programOp, progOf, Uop]
  | cons x l ih =>
    have : progOf (x :: l) = pairProg x.1 x.2 ++ progOf l := by simp [progOf]
    rw [this, programOp_append, ih, pair_op PA PB hA hB]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Uop, Matrix.mul_apply, Fin.sum_univ_two]

lemma Uop_unitary [StarRing A] [StarModule ℂ A] (PA PB : A) (hA : PA * PA = PA)
    (hB : PB * PB = PB) (hsA : IsSelfAdjoint PA) (hsB : IsSelfAdjoint PB) (s : ℝ)
    (l : List (Bool × ℝ)) : Uop PA PB s l ∈ unitary A := by
  induction l with
  | nil => simp [Uop]
  | cons x l ih =>
    simp only [Uop]
    refine Submonoid.mul_mem _ ih ?_
    cases x.1
    · exact Fop_unitary PB hB hsB _
    · exact Fop_unitary PA hA hsA _

end Circuit

section QSP
variable {A : Type*} [Ring A] [Algebra ℂ A]

noncomputable def altProd (PA PB : A) : Bool → List ℝ → A
  | _, [] => 1
  | b, φ :: ps => Fop (if b then PA else PB) φ * altProd PA PB (!b) ps

def alt : Bool → List ℝ → List (Bool × ℝ)
  | _, [] => []
  | b, φ :: ps => (b, φ) :: alt (!b) ps

lemma conj_Fop (R P : A) (hR : R * R = 1) (φ : ℝ) : R * Fop P φ * R = Fop (R * P * R) φ := by
  have hc : ∀ z : ℂ, R * algebraMap ℂ A z = algebraMap ℂ A z * R := fun z =>
    (Algebra.commutes z R).symm
  have key : ∀ (z : ℂ) (X : A), R * (algebraMap ℂ A z * X) * R = algebraMap ℂ A z * (R * X * R) := by
    intro z X
    rw [← mul_assoc R, hc, mul_assoc, mul_assoc, mul_assoc]
  simp only [Fop, mul_add, add_mul, key]
  congr 2
  rw [mul_sub, sub_mul, mul_one, hR]

lemma conj_altProd (R PA PB : A) (hR : R * R = 1) (hB : PB = R * PA * R) (b : Bool) (ps : List ℝ) :
    R * altProd PA PB b ps * R = altProd PA PB (!b) ps := by
  have hA : PA = R * PB * R := by
    rw [hB, ← mul_assoc, ← mul_assoc, hR, one_mul, mul_assoc, hR, mul_one]
  induction ps generalizing b with
  | nil => simp [altProd, hR]
  | cons φ ps ih =>
    simp only [altProd, Bool.not_not]
    have : R * (Fop (if b = true then PA else PB) φ * altProd PA PB (!b) ps) * R
        = (R * Fop (if b = true then PA else PB) φ * R) * (R * altProd PA PB (!b) ps * R) := by
      simp only [mul_assoc]; rw [← mul_assoc R R, hR, one_mul]
    rw [this, ih, conj_Fop R _ hR, Bool.not_not]
    cases b <;> simp [← hA, ← hB]

lemma qprod_eq (R PA PB : A) (hR : R * R = 1) (hB : PB = R * PA * R) (ps : List ℝ) :
    (ps.map fun φ => Fop PA φ * R).prod = altProd PA PB true ps * R ^ ps.length := by
  induction ps with
  | nil => simp [altProd]
  | cons φ ps ih =>
    simp only [List.map_cons, List.prod_cons, ih, altProd, List.length_cons, pow_succ']
    have : R * altProd PA PB true ps = (R * altProd PA PB true ps * R) * R := by
      rw [mul_assoc _ R R, hR, mul_one]
    rw [mul_assoc, ← mul_assoc R, this, conj_altProd R PA PB hR hB]
    simp [mul_assoc]

lemma altProd_append_zero (PA PB : A) (b : Bool) (ps : List ℝ) :
    altProd PA PB b (ps ++ [0]) = altProd PA PB b ps := by
  induction ps generalizing b with
  | nil => simp [altProd, Fop_zero]
  | cons φ ps ih => simp [altProd, ih]

lemma alt_count (b : Bool) (ps : List ℝ) :
    ((alt b ps).filter (·.1)).length = (if b then (ps.length + 1) / 2 else ps.length / 2) ∧
    ((alt b ps).filter (!·.1)).length = (if b then ps.length / 2 else (ps.length + 1) / 2) := by
  induction ps generalizing b with
  | nil => cases b <;> simp [alt]
  | cons φ ps ih =>
    have := ih (!b)
    cases b <;> simp_all [alt] <;> omega

end QSP

section Mat
open Matrix

lemma Fop_transpose (P : Matrix (Fin 2) (Fin 2) ℂ) (φ : ℝ) : (Fop P φ)ᵀ = Fop Pᵀ φ := by
  have hT : ∀ z : ℂ, (algebraMap ℂ (Matrix (Fin 2) (Fin 2) ℂ) z)ᵀ = algebraMap ℂ _ z := by
    intro z; simp [Matrix.algebraMap_eq_diagonal]
  simp only [Fop, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_sub,
    Matrix.transpose_one, hT]
  rw [← Algebra.commutes, ← Algebra.commutes]

lemma Uop_alt (PA PB : Matrix (Fin 2) (Fin 2) ℂ) (hA : PAᵀ = PA) (hB : PBᵀ = PB) (b : Bool)
    (ps : List ℝ) : Uop PA PB 1 (alt b ps) = (altProd PA PB b ps)ᵀ := by
  induction ps generalizing b with
  | nil => simp [alt, Uop, altProd]
  | cons φ ps ih =>
    simp only [alt, Uop, altProd, ih, Matrix.transpose_mul, Fop_transpose, one_mul]
    cases b <;> simp [hA, hB]

lemma qsp_link (d : ℕ) (hd : Odd d) (Φ : Fin d → ℝ) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    let s := Real.sqrt (1 - x ^ 2)
    let PA : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]
    let PB : Matrix (Fin 2) (Fin 2) ℂ := !![(x : ℂ) ^ 2, x * s; x * s, (s : ℂ) ^ 2]
    let M := Uop PA PB 1 (alt true (List.ofFn Φ ++ [0]))
    (x : ℂ) * M 0 0 + (s : ℂ) * M 1 0 = QSVT19.Main.qspRefl Φ x 0 0 := by
  intro s PA PB M
  set R := QSVT19.Main.reflR x with hRdef
  have hRm : R = !![(x : ℂ), (s : ℂ); (s : ℂ), -(x : ℂ)] := rfl
  have hs2 : (s : ℂ) ^ 2 = 1 - (x : ℂ) ^ 2 := by
    have : s ^ 2 = 1 - x ^ 2 := Real.sq_sqrt (by nlinarith [hx.1, hx.2])
    exact_mod_cast this
  have hR : R * R = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [hRm, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | linear_combination hs2 | linear_combination (0 : ℂ) * hs2
  have hB : PB = R * PA * R := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [hRm, PA, PB, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hZ : ∀ φ : ℝ, QAlgorithms.qspZ φ = Fop PA φ := by
    intro φ
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [QAlgorithms.qspZ, Fop, PA, Matrix.algebraMap_eq_diagonal]
  have hq : QSVT19.Main.qspRefl Φ x = altProd PA PB true (List.ofFn Φ) * R := by
    unfold QSVT19.Main.qspRefl
    have : (List.ofFn fun j : Fin d => QAlgorithms.qspZ (Φ j) * QSVT19.Main.reflR x)
        = (List.ofFn Φ).map (fun φ => Fop PA φ * R) := by
      rw [List.map_ofFn]; congr 1; funext j; simp [hZ, R]
    rw [this, qprod_eq R PA PB hR hB, List.length_ofFn]
    obtain ⟨k, rfl⟩ := hd
    rw [pow_succ, pow_mul, sq, hR, one_pow, one_mul]
  have hM : M = (altProd PA PB true (List.ofFn Φ))ᵀ := by
    simp only [M]
    rw [Uop_alt PA PB (by ext i j; fin_cases i <;> fin_cases j <;> simp [PA])
      (by ext i j; fin_cases i <;> fin_cases j <;> simp [PB]), altProd_append_zero]
  rw [hq, hM]
  simp [Matrix.mul_apply, Fin.sum_univ_two, hRm]
  ring

end Mat

section PolySec
open Polynomial

/-! ### Chebyshev facts -/

lemma T_sin (k : ℕ) (α : ℝ) :
    (Chebyshev.T ℝ ((2 * k + 1 : ℕ) : ℤ)).eval (Real.sin α) =
      (-1) ^ k * Real.sin ((2 * k + 1 : ℕ) * α) := by
  rw [← Real.cos_pi_div_two_sub, Chebyshev.T_real_cos]
  have e : (((2 * k + 1 : ℕ) : ℤ) : ℝ) * (Real.pi / 2 - α)
      = ((k : ℝ) * Real.pi + Real.pi / 2) - ((2 * k + 1 : ℕ) : ℝ) * α := by push_cast; ring
  rw [e, Real.cos_sub, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two, Real.sin_nat_mul_pi,
    Real.cos_nat_mul_pi]
  ring

lemma abs_sin_nat_mul_le (n : ℕ) (α : ℝ) : |Real.sin (n * α)| ≤ n * |Real.sin α| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : ((n + 1 : ℕ) : ℝ) * α = n * α + α := by push_cast; ring
    rw [e, Real.sin_add]
    calc |Real.sin (n * α) * Real.cos α + Real.cos (n * α) * Real.sin α|
        ≤ |Real.sin (n * α)| * |Real.cos α| + |Real.cos (n * α)| * |Real.sin α| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ |Real.sin (n * α)| * 1 + 1 * |Real.sin α| := by
          gcongr
          · exact Real.abs_cos_le_one _
          · exact Real.abs_cos_le_one _
      _ ≤ _ := by push_cast; nlinarith [abs_nonneg (Real.sin α)]

/-- `T_{2k+1}(t)/t` as a polynomial. -/
noncomputable def Sk (k : ℕ) : ℝ[X] := (Chebyshev.T ℝ ((2 * k + 1 : ℕ) : ℤ)).divX

lemma T_coeff_zero (k : ℕ) : (Chebyshev.T ℝ ((2 * k + 1 : ℕ) : ℤ)).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero, ← Real.sin_zero, T_sin]; simp

lemma Sk_mul (k : ℕ) (t : ℝ) :
    (Sk k).eval t * t = (Chebyshev.T ℝ ((2 * k + 1 : ℕ) : ℤ)).eval t := by
  conv_rhs => rw [← divX_mul_X_add (Chebyshev.T ℝ ((2 * k + 1 : ℕ) : ℤ)), T_coeff_zero]
  simp [Sk]

lemma Sk_bounds (k : ℕ) (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    |(Sk k).eval t| ≤ 1 / t ∧ |(Sk k).eval t| ≤ (2 * k + 1 : ℕ) ∧
      (t ≤ 1 / (2 * k + 1 : ℕ) → 2 * (2 * k + 1 : ℕ) / Real.pi ≤ |(Sk k).eval t|) := by
  set m : ℕ := 2 * k + 1 with hm
  have hm1 : (1 : ℝ) ≤ m := by rw [hm]; push_cast; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  set α := Real.arcsin t with hα
  have hsin : Real.sin α = t := Real.sin_arcsin (by linarith) ht1
  have hT : (Chebyshev.T ℝ (m : ℤ)).eval t = (-1) ^ k * Real.sin (m * α) := by
    rw [← hsin, hm, T_sin]
  have habsT : |(Chebyshev.T ℝ (m : ℤ)).eval t| = |Real.sin (m * α)| := by
    rw [hT, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hS : |(Sk k).eval t| = |Real.sin (m * α)| / t := by
    rw [← habsT, ← Sk_mul k t, abs_mul, abs_of_pos ht0]; field_simp
  refine ⟨?_, ?_, ?_⟩
  · rw [hS]; gcongr; exact Real.abs_sin_le_one _
  · rw [hS, div_le_iff₀ ht0]
    have := abs_sin_nat_mul_le m α
    rw [hsin, abs_of_pos ht0] at this; exact this
  · intro htm
    have hα0 : 0 ≤ α := Real.arcsin_nonneg.mpr ht0.le
    have hαt : t ≤ α := by
      have := Real.sin_le hα0; rw [hsin] at this; exact this
    -- arcsin t ≤ π t / 2
    have hαle : α ≤ Real.pi / 2 * t := by
      rw [hα, Real.arcsin_le_iff_le_sin ⟨by linarith, ht1⟩
        ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩]
      have := Real.mul_le_sin (x := Real.pi / 2 * t) (by positivity) (by nlinarith [Real.pi_pos])
      have e : 2 / Real.pi * (Real.pi / 2 * t) = t := by field_simp
      linarith
    have hmα : m * α ≤ Real.pi / 2 := by
      calc m * α ≤ m * (Real.pi / 2 * t) := by gcongr
        _ = Real.pi / 2 * (m * t) := by ring
        _ ≤ Real.pi / 2 * 1 := by
          gcongr
          rw [le_div_iff₀ (by linarith)] at htm; linarith
        _ = _ := by ring
    have h1 := Real.mul_le_sin (by positivity) hmα
    have hpos : 0 ≤ Real.sin (m * α) := by linarith [show 0 ≤ 2 / Real.pi * (m * α) by positivity]
    rw [hS, abs_of_nonneg hpos, le_div_iff₀ ht0]
    calc 2 * (m : ℝ) / Real.pi * t ≤ 2 * m / Real.pi * α := by gcongr
      _ = 2 / Real.pi * (m * α) := by ring
      _ ≤ _ := h1

lemma Sk_even (k : ℕ) (t : ℝ) (ht : t ≠ 0) : (Sk k).eval (-t) = (Sk k).eval t := by
  have h1 := Sk_mul k t
  have h2 := Sk_mul k (-t)
  rw [Chebyshev.T_eval_neg] at h2
  have : ((((2 * k + 1 : ℕ) : ℤ)).negOnePow : ℝ) = -1 := by
    rw [Int.negOnePow_odd]; · simp
    exact ⟨k, by push_cast; ring⟩
  rw [this, ← h1] at h2
  have : ((Sk k).eval (-t) - (Sk k).eval t) * t = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · exact absurd h ht

lemma Sk_natDegree (k : ℕ) : (Sk k).natDegree = 2 * k := by
  rw [Sk, natDegree_divX_eq_natDegree_tsub_one, Chebyshev.natDegree_T, Int.natAbs_natCast]; omega

/-! ### Antiderivative -/

noncomputable def anti (p : ℝ[X]) : ℝ[X] :=
  ∑ i ∈ Finset.range (p.natDegree + 1), C (p.coeff i / (i + 1)) * X ^ (i + 1)

lemma derivative_anti (p : ℝ[X]) : derivative (anti p) = p := by
  rw [anti, derivative_sum]
  conv_rhs => rw [p.as_sum_range_C_mul_X_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [derivative_C_mul_X_pow]
  congr 1
  · congr 1; push_cast; field_simp

lemma anti_eval_zero (p : ℝ[X]) : (anti p).eval 0 = 0 := by
  simp [anti, eval_finsetSum]

lemma anti_natDegree (p : ℝ[X]) : (anti p).natDegree ≤ p.natDegree + 1 := by
  rw [anti]
  refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_X_pow]; simp at hi; omega

lemma anti_hasDeriv (p : ℝ[X]) (x : ℝ) : HasDerivAt (fun t => (anti p).eval t) (p.eval x) x := by
  have := (anti p).hasDerivAt x
  rwa [derivative_anti] at this

lemma anti_odd (p : ℝ[X]) (h : p.comp (-X) = p) : (anti p).comp (-X) = -anti p := by
  have hd : derivative ((anti p).comp (-X) + anti p) = 0 := by
    rw [derivative_add, derivative_comp, derivative_anti, h]; simp
  have h0 := (derivative_eq_zero.mp hd)
  rw [natDegree_eq_zero] at h0
  obtain ⟨c, hc⟩ := h0
  have hc0 : c = 0 := by
    have := congrArg (eval 0) hc
    simp [eval_comp, anti_eval_zero] at this; linarith
  rw [hc0, C_0] at hc
  exact eq_neg_of_add_eq_zero_left hc.symm

/-- Upper bound for the tail of the antiderivative under `K t ≤ 1/t^(2r)`. -/
lemma anti_tail (K : ℝ[X]) (r : ℕ) (hr : 1 ≤ r) (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hK : ∀ t, x ≤ t → t ≤ 1 → K.eval t ≤ 1 / t ^ (2 * r)) :
    (anti K).eval 1 - (anti K).eval x ≤ 1 / ((2 * r - 1) * x ^ (2 * r - 1)) := by
  set n := 2 * r - 1 with hn
  have hn1 : 1 ≤ n := by omega
  have hnR : ((n : ℕ) : ℝ) = 2 * r - 1 := by rw [hn]; push_cast [show 1 ≤ 2 * r by omega]; ring
  let g : ℝ → ℝ := fun t => (anti K).eval t + 1 / ((n : ℝ) * t ^ n)
  have hg : ∀ t, 0 < t → HasDerivAt g (K.eval t - 1 / t ^ (2 * r)) t := by
    intro t ht
    have h1 := anti_hasDeriv K t
    have h2 : HasDerivAt (fun t : ℝ => 1 / ((n : ℝ) * t ^ n)) (-(1 / t ^ (2 * r))) t := by
      have h3 : HasDerivAt (fun t : ℝ => (n : ℝ) * t ^ n) ((n : ℝ) * (n * t ^ (n - 1))) t :=
        (hasDerivAt_pow n t).const_mul _
      have h4 := h3.inv (by positivity)
      have e : (fun t : ℝ => 1 / ((n : ℝ) * t ^ n)) = fun t => ((n : ℝ) * t ^ n)⁻¹ := by
        funext t; simp
      rw [e]
      refine h4.congr_deriv ?_
      have e2 : 2 * r = n + 1 := by omega
      rw [e2]
      have : t ^ n = t ^ (n - 1) * t := by rw [← pow_succ]; congr 1; omega
      rw [this]
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      field_simp
      rw [pow_succ, this]; ring
    exact (h1.add h2).congr_deriv (by ring)
  have hanti : AntitoneOn g (Set.Icc x 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc x 1)
    · intro t ht
      exact (hg t (by linarith [ht.1])).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hg t (by linarith [ht.1])).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hg t (by linarith [ht.1])).deriv]
      linarith [hK t ht.1.le ht.2.le]
  have := hanti ⟨le_refl x, hx1⟩ ⟨hx1, le_refl 1⟩ hx1
  simp only [g, one_pow, mul_one] at this
  rw [← hnR]
  have : 0 < 1 / (n : ℝ) := by positivity
  linarith

/-- Linear lower/upper bounds from derivative bounds on an interval. -/
lemma anti_lower (K : ℝ[X]) (x y c : ℝ) (hxy : x ≤ y) (hK : ∀ t, x < t → t < y → c ≤ K.eval t) :
    c * (y - x) ≤ (anti K).eval y - (anti K).eval x := by
  have := (convex_Icc x y).mul_sub_le_image_sub_of_le_deriv (f := fun t => (anti K).eval t)
    (anti K).continuous.continuousOn (anti K).differentiable.differentiableOn (C := c) ?_
    x ⟨le_refl x, hxy⟩ y ⟨hxy, le_refl y⟩ hxy
  · exact this
  · intro t ht; rw [interior_Icc] at ht
    rw [(anti_hasDeriv K t).deriv]; exact hK t ht.1 ht.2

lemma anti_upper (K : ℝ[X]) (x y c : ℝ) (hxy : x ≤ y) (hK : ∀ t, x < t → t < y → K.eval t ≤ c) :
    (anti K).eval y - (anti K).eval x ≤ c * (y - x) := by
  have := (convex_Icc x y).image_sub_le_mul_sub_of_deriv_le (f := fun t => (anti K).eval t)
    (anti K).continuous.continuousOn (anti K).differentiable.differentiableOn (C := c) ?_
    x ⟨le_refl x, hxy⟩ y ⟨hxy, le_refl y⟩ hxy
  · exact this
  · intro t ht; rw [interior_Icc] at ht
    rw [(anti_hasDeriv K t).deriv]; exact hK t ht.1 ht.2

lemma anti_mono (K : ℝ[X]) (hK : ∀ t, 0 ≤ K.eval t) : Monotone fun t => (anti K).eval t := by
  apply monotone_of_deriv_nonneg (anti K).differentiable
  intro t; rw [(anti_hasDeriv K t).deriv]; exact hK t


/-! ### The kernel `(T_m(t)/t)^(2r)` -/

lemma K_facts (k r : ℕ) (hr : 1 ≤ r) :
    (∀ t, 0 ≤ ((Sk k) ^ (2 * r)).eval t) ∧ ((Sk k) ^ (2 * r)).comp (-X) = (Sk k) ^ (2 * r) ∧
    (∀ t, 0 < t → t ≤ 1 → ((Sk k) ^ (2 * r)).eval t ≤ 1 / t ^ (2 * r)) ∧
    (∀ t, 0 < t → t ≤ 1 → ((Sk k) ^ (2 * r)).eval t ≤ ((2 * k + 1 : ℕ) : ℝ) ^ (2 * r)) ∧
    (∀ t, 0 < t → t ≤ 1 / ((2 * k + 1 : ℕ) : ℝ) →
      (2 * ((2 * k + 1 : ℕ) : ℝ) / Real.pi) ^ (2 * r) ≤ ((Sk k) ^ (2 * r)).eval t) := by
  have hev : ∀ t, ((Sk k) ^ (2 * r)).eval t = |(Sk k).eval t| ^ (2 * r) := by
    intro t; rw [eval_pow, (even_two_mul r).pow_abs]
  have hm1 : (1 : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) := by push_cast; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  refine ⟨fun t => by rw [hev]; positivity, ?_, ?_, ?_, ?_⟩
  · apply eq_of_infinite_eval_eq
    apply Set.Infinite.mono _ (Set.Ioi_infinite (0 : ℝ))
    intro t ht
    simp only [Set.mem_ofPred_eq, eval_comp, eval_neg, eval_X, eval_pow]
    rw [Sk_even k t (ne_of_gt ht)]
  · intro t h0 h1
    rw [hev, one_div, ← inv_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (by rw [← one_div]; exact (Sk_bounds k t h0 h1).1) _
  · intro t h0 h1
    rw [hev]
    exact pow_le_pow_left₀ (abs_nonneg _) (Sk_bounds k t h0 h1).2.1 _
  · intro t h0 h1
    have h1' : t ≤ 1 := h1.trans (by rw [div_le_one (by linarith)]; exact hm1)
    rw [hev]
    exact pow_le_pow_left₀ (by positivity) ((Sk_bounds k t h0 h1').2.2 h1) _

/-! ### Normalization -/

lemma norm_props (K : ℝ[X]) (hK0 : ∀ t, 0 ≤ K.eval t) (heven : K.comp (-X) = K)
    (hH1 : 0 < (anti K).eval 1) :
    Odd (C ((anti K).eval 1)⁻¹ * anti K).natDegree ∧
    (C ((anti K).eval 1)⁻¹ * anti K).natDegree ≤ K.natDegree + 1 ∧
    (C ((anti K).eval 1)⁻¹ * anti K).comp (-X) = -(C ((anti K).eval 1)⁻¹ * anti K) ∧
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, |(C ((anti K).eval 1)⁻¹ * anti K).eval x| ≤ 1) ∧
    (∀ x : ℝ, 1 ≤ |x| → 1 ≤ |(C ((anti K).eval 1)⁻¹ * anti K).eval x|) ∧
    ∀ x, (C ((anti K).eval 1)⁻¹ * anti K).eval x = (anti K).eval x / (anti K).eval 1 := by
  set H := anti K
  set H1 := H.eval 1
  set P := C H1⁻¹ * H with hP
  have hodd : H.comp (-X) = -H := anti_odd K heven
  have hHneg : ∀ x, H.eval (-x) = -H.eval x := by
    intro x
    have := congrArg (eval x) hodd
    simpa [eval_comp] using this
  have hmono := anti_mono K hK0
  have hPe : ∀ x, P.eval x = H.eval x / H1 := by
    intro x; simp [hP, div_eq_inv_mul]
  have hPodd : P.comp (-X) = -P := by
    rw [hP, mul_comp, C_comp, hodd]; ring
  have hPne : P ≠ 0 := by
    intro h; have := hPe 1; rw [h, eval_zero, div_self hH1.ne'] at this; exact zero_ne_one this
  refine ⟨?_, ?_, hPodd, ?_, ?_, hPe⟩
  · have hlc := comp_neg_X_leadingCoeff_eq P
    rw [hPodd, leadingCoeff_neg] at hlc
    have hl : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hPne
    have : ((-1 : ℝ) ^ P.natDegree) = -1 := by
      have h2 : ((-1 : ℝ) ^ P.natDegree + 1) * P.leadingCoeff = 0 := by linear_combination -hlc
      rcases mul_eq_zero.mp h2 with h | h
      · linarith
      · exact absurd h hl
    exact (neg_one_pow_eq_neg_one_iff_odd (by norm_num)).mp this
  · calc P.natDegree ≤ H.natDegree := by rw [hP]; exact natDegree_C_mul_le _ _
      _ ≤ _ := anti_natDegree K
  · intro x hx
    rw [hPe, abs_div, abs_of_pos hH1, div_le_one hH1, abs_le]
    constructor
    · have := hmono hx.1; simp only at this; rw [hHneg] at this; linarith
    · exact hmono hx.2
  · intro x hx
    rw [hPe, abs_div, abs_of_pos hH1, le_div_iff₀ hH1, one_mul]
    rcases le_abs'.mp hx with h | h
    · have := hmono h; simp only at this; rw [hHneg] at this
      rw [abs_of_neg (by linarith)]; linarith
    · have := hmono h; simp only at this
      rw [abs_of_pos (by linarith)]; linarith


lemma log_ge (ε : ℝ) (h0 : 0 < ε) : 1 - ε ≤ Real.log (1 / ε) := by
  have := Real.one_sub_inv_le_log_of_pos (x := 1 / ε) (by positivity)
  simpa using this

abbrev PolyGoal (c ε δ : ℝ) : Prop :=
    ∃ (d : ℕ) (P : Polynomial ℝ), Odd d ∧ P.natDegree = d ∧
      ((d : ℝ) + 1 ≤ c * (Real.log (1 / ε) / δ)) ∧
      P.comp (-Polynomial.X) = -P ∧ (∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ 1) ∧
      (∀ x : ℝ, 1 ≤ |x| → 1 ≤ |P.eval x|) ∧ ∀ x ∈ Set.Icc δ 1, 1 - ε ≤ P.eval x

lemma caseB (ε δ : ℝ) (h0 : 0 < ε) (h1 : ε < 1) (h2 : 0 < δ) (h3 : δ < 1) (hδ : δ < 1 - ε)
    (hη : 1 - ε ≤ 1 / 8) : PolyGoal 16 ε δ := by
  set η := 1 - ε with hηdef
  set k : ℕ := ⌈Real.pi ^ 2 * η / (4 * δ)⌉₊ with hkdef
  have hk1 : Real.pi ^ 2 * η / (4 * δ) ≤ k := Nat.le_ceil _
  have hk2 : (k : ℝ) < Real.pi ^ 2 * η / (4 * δ) + 1 := Nat.ceil_lt_add_one (by positivity)
  set m : ℝ := ((2 * k + 1 : ℕ) : ℝ) with hmdef
  have hm : m = 2 * k + 1 := by rw [hmdef]; push_cast; ring
  have hpi1 : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi0 : 3 < Real.pi := Real.pi_gt_three
  have hm1 : 1 ≤ m := by rw [hm]; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hδm : δ * m ≤ 1 := by
    have e : δ * (Real.pi ^ 2 * η / (4 * δ)) = Real.pi ^ 2 * η / 4 := by field_simp
    have : δ * k < Real.pi ^ 2 * η / 4 + δ := by
      have := mul_lt_mul_of_pos_left hk2 h2; rw [mul_add, e] at this; linarith
    rw [hm]; nlinarith
  have hmδ : δ ≤ 1 / m := by rw [le_div_iff₀ (by linarith)]; linarith
  have hmη : Real.pi ^ 2 * η ≤ 2 * m * δ := by
    have e : δ * (Real.pi ^ 2 * η / (4 * δ)) = Real.pi ^ 2 * η / 4 := by field_simp
    have := mul_le_mul_of_nonneg_left hk1 h2.le; rw [e] at this
    rw [hm]; nlinarith
  obtain ⟨hK0, hKev, hKtail, hKup, hKlow⟩ := K_facts k 1 le_rfl
  set K := (Sk k) ^ (2 * 1)
  set H := anti K
  have hH0 : H.eval 0 = 0 := anti_eval_zero K
  have hlow : (2 * m / Real.pi) ^ (2 * 1) * (δ - 0) ≤ H.eval δ - H.eval 0 :=
    anti_lower K 0 δ _ h2.le fun t ht0 ht1 => hKlow t ht0 (by linarith)
  have hlowm : (2 * m / Real.pi) ^ (2 * 1) * (1 / m - 0) ≤ H.eval (1 / m) - H.eval 0 :=
    anti_lower K 0 (1 / m) _ (by positivity) fun t ht0 ht1 => hKlow t ht0 ht1.le
  have hupm : H.eval (1 / m) - H.eval 0 ≤ m ^ (2 * 1) * (1 / m - 0) :=
    anti_upper K 0 (1 / m) _ (by positivity) fun t ht0 ht1 =>
      hKup t ht0 (ht1.le.trans (by rw [div_le_one (by linarith)]; exact hm1))
  have htail := anti_tail K 1 le_rfl (1 / m) (by positivity)
    (by rw [div_le_one (by linarith)]; exact hm1)
    fun t ht0 ht1 => hKtail t (lt_of_lt_of_le (by positivity) ht0) ht1
  have hmono := anti_mono K hK0
  have hm1' : 1 / m ≤ 1 := by rw [div_le_one (by linarith)]; exact hm1
  have hHm_pos : 0 < H.eval (1 / m) := by
    rw [hH0] at hlowm
    have : 0 < (2 * m / Real.pi) ^ (2 * 1) * (1 / m - 0) :=
      mul_pos (pow_pos (div_pos (by linarith) Real.pi_pos) _)
        (by rw [sub_zero]; exact one_div_pos.mpr (by linarith))
    linarith
  have hH1 : 0 < H.eval 1 := lt_of_lt_of_le hHm_pos (hmono hm1')
  have hH1le : H.eval 1 ≤ 2 * m := by
    have e1 : m ^ (2 * 1) * (1 / m - 0) = m := by
      have : m ≠ 0 := by linarith
      rw [sub_zero]; field_simp
    have e2 : 1 / ((2 * (1 : ℕ) - 1 : ℝ) * (1 / m) ^ (2 * 1 - 1)) = m := by norm_num
    rw [e1, hH0] at hupm; rw [e2] at htail; linarith
  obtain ⟨hdodd, hddeg, hPodd, hPle, hPge, hPe⟩ := norm_props K hK0 hKev hH1
  refine ⟨_, _, hdodd, rfl, ?_, hPodd, hPle, hPge, ?_⟩
  · have hKdeg : K.natDegree ≤ 2 * 1 * (2 * k) := by
      rw [← Sk_natDegree k]; exact natDegree_pow_le
    have hd : ((C (H.eval 1)⁻¹ * H).natDegree : ℝ) ≤ 4 * k + 1 := by
      have h' : (C (H.eval 1)⁻¹ * H).natDegree ≤ 4 * k + 1 :=
        calc _ ≤ K.natDegree + 1 := hddeg
          _ ≤ 2 * 1 * (2 * k) + 1 := Nat.add_le_add_right hKdeg 1
          _ = 4 * k + 1 := by ring
      exact_mod_cast h'
    have hL := log_ge ε h0
    have hηδ : 1 < η / δ := by rw [lt_div_iff₀ h2]; linarith
    rw [mul_div_assoc']
    rw [le_div_iff₀ h2]
    have : (4 * k + 2) * δ ≤ 16 * η := by
      have e : δ * (Real.pi ^ 2 * η / (4 * δ)) = Real.pi ^ 2 * η / 4 := by field_simp
      have := mul_lt_mul_of_pos_left hk2 h2; rw [mul_add, e] at this
      have hpi2 : Real.pi ^ 2 < 10 := by nlinarith
      have : Real.pi ^ 2 * η ≤ 10 * η := by nlinarith
      have e2 : (4 * (k : ℝ) + 2) * δ = 4 * (δ * k) + 2 * δ := by ring
      linarith
    calc ((C (H.eval 1)⁻¹ * H).natDegree + 1 : ℝ) * δ ≤ (4 * k + 2) * δ :=
          mul_le_mul_of_nonneg_right (by linarith) h2.le
      _ ≤ 16 * η := this
      _ ≤ 16 * Real.log (1 / ε) := by linarith
  · intro x hx
    rw [hPe, le_div_iff₀ hH1]
    have hHx : H.eval δ ≤ H.eval x := hmono hx.1
    rw [hH0, sub_zero, sub_zero] at hlow
    have : (2 * m / Real.pi) ^ (2 * 1) * δ = 4 * m * (m * δ) / Real.pi ^ 2 := by ring
    rw [this] at hlow
    have hη' : η * Real.pi ^ 2 ≤ 2 * m * δ := by linarith
    have : η * H.eval 1 ≤ η * (2 * m) := mul_le_mul_of_nonneg_left hH1le (by linarith)
    have : η * (2 * m) ≤ 4 * m * (m * δ) / Real.pi ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      calc η * (2 * m) * Real.pi ^ 2 = 2 * m * (Real.pi ^ 2 * η) := by ring
        _ ≤ 2 * m * (2 * m * δ) := mul_le_mul_of_nonneg_left hmη (by linarith)
        _ = 4 * m * (m * δ) := by ring
    linarith


lemma caseC (ε δ : ℝ) (h0 : 0 < ε) (h1 : ε < 1) (h2 : 0 < δ) (h3 : δ < 1)
    (hη : 1 / 8 < 1 - ε) : PolyGoal 264 ε δ := by
  set L := Real.log (1 / ε) with hLdef
  have hL : 1 - ε ≤ L := log_ge ε h0
  set k : ℕ := ⌈5 / (2 * δ)⌉₊ with hkdef
  have hk1 : 5 / (2 * δ) ≤ k := Nat.le_ceil _
  have hk2 : (k : ℝ) < 5 / (2 * δ) + 1 := Nat.ceil_lt_add_one (by positivity)
  set r : ℕ := ⌈(L + 2) / 2⌉₊ with hrdef
  have hr1 : (L + 2) / 2 ≤ r := Nat.le_ceil _
  have hr2 : (r : ℝ) < (L + 2) / 2 + 1 := Nat.ceil_lt_add_one (by linarith)
  have hr : 1 ≤ r := by
    have : (1 : ℝ) ≤ r := by linarith
    exact_mod_cast this
  set m : ℝ := ((2 * k + 1 : ℕ) : ℝ) with hmdef
  have hm : m = 2 * k + 1 := by rw [hmdef]; push_cast; ring
  have hkδ1 : 5 / 2 ≤ δ * k := by
    have e : δ * (5 / (2 * δ)) = 5 / 2 := by field_simp
    have := mul_le_mul_of_nonneg_left hk1 h2.le; rw [e] at this; exact this
  have hkδ2 : δ * k < 5 / 2 + δ := by
    have e : δ * (5 / (2 * δ)) = 5 / 2 := by field_simp
    have := mul_lt_mul_of_pos_left hk2 h2; rw [mul_add, e, mul_one] at this; exact this
  have hm1 : 1 ≤ m := by rw [hm]; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hm0 : 0 < m := by linarith
  have hu : 5 ≤ m * δ := by rw [hm]; nlinarith
  have hu2 : m * δ < 8 := by rw [hm]; nlinarith
  obtain ⟨hK0, hKev, hKtail, -, hKlow⟩ := K_facts k r hr
  set K := (Sk k) ^ (2 * r)
  set H := anti K
  have hH0 : H.eval 0 = 0 := anti_eval_zero K
  have hm1' : 1 / m ≤ 1 := by rw [div_le_one hm0]; exact hm1
  have hlowm : (2 * m / Real.pi) ^ (2 * r) * (1 / m - 0) ≤ H.eval (1 / m) - H.eval 0 :=
    anti_lower K 0 (1 / m) _ (by positivity) fun t ht0 ht1 => hKlow t ht0 ht1.le
  rw [hH0, sub_zero, sub_zero] at hlowm
  set F := (2 * m / Real.pi) ^ (2 * r) * (1 / m) with hF
  have hF0 : 0 < F := mul_pos (pow_pos (div_pos (by linarith) Real.pi_pos) _) (by positivity)
  have hmono := anti_mono K hK0
  have hH1F : F ≤ H.eval 1 := hlowm.trans (hmono hm1')
  have hH1 : 0 < H.eval 1 := lt_of_lt_of_le hF0 hH1F
  have htail := anti_tail K r hr δ h2 h3.le fun t ht0 ht1 => hKtail t (by linarith) ht1
  set n := 2 * r - 1 with hn
  have hn2 : 2 * r = n + 1 := by omega
  have hnR : (2 * (r : ℝ) - 1) = n := by
    rw [hn]; push_cast [show 1 ≤ 2 * r by omega]; ring
  have hδn : 0 < δ ^ n := pow_pos h2 n
  have htail' : H.eval 1 - H.eval δ ≤ 1 / δ ^ n := by
    refine htail.trans ?_
    rw [hnR]
    have : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    gcongr
    nlinarith
  -- the key estimate `1/δ^n ≤ ε F`
  have hkey : 1 / δ ^ n ≤ ε * F := by
    have hexp1 : Real.exp 1 ≤ 10 / Real.pi := by
      rw [le_div_iff₀ Real.pi_pos]
      have := Real.exp_one_lt_d9; have := Real.pi_lt_d2; nlinarith [Real.exp_pos 1]
    have hE : Real.exp ((n + 1 : ℕ) : ℝ) ≤ (10 / Real.pi) ^ (n + 1) := by
      rw [← Real.exp_one_pow]; exact pow_le_pow_left₀ (Real.exp_pos 1).le hexp1 _
    have hLe : Real.exp (L + 2) ≤ Real.exp ((n + 1 : ℕ) : ℝ) := by
      apply Real.exp_le_exp.mpr
      rw [← hn2]; push_cast; linarith
    have hexpL : Real.exp (L + 2) = (1 / ε) * Real.exp 2 := by
      rw [Real.exp_add, hLdef, Real.exp_log (by positivity)]
    have hexp2 : 5 ≤ Real.exp 2 := by
      have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [Real.exp_one_pow]; norm_num
      rw [this]; have := Real.exp_one_gt_d9; nlinarith
    have hFe : F * δ ^ n = (2 / Real.pi) ^ (n + 1) * (m * δ) ^ n := by
      rw [hF, hn2]; field_simp; ring
    have hpow : (5 : ℝ) ^ n ≤ (m * δ) ^ n := pow_le_pow_left₀ (by norm_num) hu n
    have h10 : (2 / Real.pi) ^ (n + 1) * 5 ^ n * 5 = (10 / Real.pi) ^ (n + 1) := by
      rw [mul_assoc, ← pow_succ, ← mul_pow]; congr 1; ring
    rw [div_le_iff₀ hδn, mul_assoc, hFe]
    have hA : 0 < (2 / Real.pi) ^ (n + 1) := pow_pos (div_pos two_pos Real.pi_pos) _
    calc (1 : ℝ) ≤ ε * ((1 / ε) * Real.exp 2) / 5 := by
          rw [← mul_assoc, mul_one_div_cancel h0.ne', one_mul, le_div_iff₀ (by norm_num)]; linarith
      _ ≤ ε * (10 / Real.pi) ^ (n + 1) / 5 := by
          gcongr; rw [← hexpL]; exact hLe.trans hE
      _ = ε * ((2 / Real.pi) ^ (n + 1) * 5 ^ n) := by rw [← h10]; ring
      _ ≤ ε * ((2 / Real.pi) ^ (n + 1) * (m * δ) ^ n) := by gcongr
  obtain ⟨hdodd, hddeg, hPodd, hPle, hPge, hPe⟩ := norm_props K hK0 hKev hH1
  refine ⟨_, _, hdodd, rfl, ?_, hPodd, hPle, hPge, ?_⟩
  · have hKdeg : K.natDegree ≤ 2 * r * (2 * k) := by
      rw [← Sk_natDegree k]; exact natDegree_pow_le
    have h' : (C (H.eval 1)⁻¹ * H).natDegree + 1 ≤ 2 * r * (2 * k + 1) :=
      calc _ ≤ K.natDegree + 1 + 1 := Nat.add_le_add_right hddeg 1
        _ ≤ 2 * r * (2 * k) + 1 + 1 := by omega
        _ ≤ 2 * r * (2 * k) + 2 * r := by omega
        _ = 2 * r * (2 * k + 1) := by ring
    have hd : ((C (H.eval 1)⁻¹ * H).natDegree + 1 : ℝ) ≤ 2 * r * m := by
      rw [hm]; exact_mod_cast h'
    rw [mul_div_assoc', le_div_iff₀ h2]
    calc ((C (H.eval 1)⁻¹ * H).natDegree + 1 : ℝ) * δ ≤ 2 * r * m * δ :=
          mul_le_mul_of_nonneg_right hd h2.le
      _ = 2 * r * (m * δ) := by ring
      _ ≤ 2 * r * 8 := by gcongr
      _ ≤ 264 * L := by linarith
  · intro x hx
    rw [hPe, le_div_iff₀ hH1]
    have hHx : H.eval δ ≤ H.eval x := hmono hx.1
    have : ε * F ≤ ε * H.eval 1 := mul_le_mul_of_nonneg_left hH1F h0.le
    have e : (1 - ε) * H.eval 1 = H.eval 1 - ε * H.eval 1 := by ring
    rw [e]; linarith

lemma poly_exists : ∃ c : ℝ, 0 < c ∧ ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 → δ < 1 - ε →
    ∃ (d : ℕ) (P : Polynomial ℝ), Odd d ∧ P.natDegree = d ∧
      ((d : ℝ) + 1 ≤ c * (Real.log (1 / ε) / δ)) ∧
      P.comp (-Polynomial.X) = -P ∧ (∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ 1) ∧
      (∀ x : ℝ, 1 ≤ |x| → 1 ≤ |P.eval x|) ∧ ∀ x ∈ Set.Icc δ 1, 1 - ε ≤ P.eval x := by
  refine ⟨264, by norm_num, fun ε δ h0 h1 h2 h3 hδ => ?_⟩
  have hLδ : 0 ≤ Real.log (1 / ε) / δ :=
    div_nonneg (Real.log_nonneg (by rw [le_div_iff₀ h0]; linarith)) h2.le
  by_cases hη : 1 - ε ≤ 1 / 8
  · obtain ⟨d, P, a, b, hb, rest⟩ := caseB ε δ h0 h1 h2 h3 hδ hη
    exact ⟨d, P, a, b, hb.trans (by nlinarith), rest⟩
  · exact caseC ε δ h0 h1 h2 h3 (lt_of_not_ge hη)

end PolySec

lemma evalC (P : Polynomial ℝ) (x : ℝ) :
    (P.map Complex.ofRealHom).eval (x : ℂ) = ((P.eval x : ℝ) : ℂ) := by
  rw [Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply Complex.ofRealHom x

lemma core_phases : ∃ c : ℝ, 0 < c ∧ ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
    ∃ l : List (Bool × ℝ), (l.filter (·.1)).length = (l.filter (!·.1)).length ∧
      (2 * (l.filter (·.1)).length : ℝ) ≤ c * (Real.log (1 / ε) / δ) ∧
      ∀ ς : ℝ, 0 ≤ ς → ς ≤ 1 →
        let s := Real.sqrt (1 - ς ^ 2)
        let PA : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]
        let PB : Matrix (Fin 2) (Fin 2) ℂ := !![(ς : ℂ) ^ 2, ς * s; ς * s, (s : ℂ) ^ 2]
        let M := Uop PA PB 1 l
        ∃ r : ℝ, ((ς : ℂ) * M 0 0 + (s : ℂ) * M 1 0 = r) ∧ (δ ≤ ς → 1 - ε ≤ r ∧ r ≤ 1) := by
  obtain ⟨c, hc, hP⟩ := poly_exists
  refine ⟨c, hc, fun ε δ h0 h1 h2 h3 => ?_⟩
  have hL : 0 < Real.log (1 / ε) := Real.log_pos (by rw [lt_div_iff₀ h0]; linarith)
  by_cases hcase : δ < 1 - ε
  · obtain ⟨d, P, hd, hdeg, hbound, hodd, hle, hge, happrox⟩ := hP ε δ h0 h1 h2 h3 hcase
    have hd1 : 1 ≤ d := hd.pos
    have hreq : QSVT19.Main.Cor8Requirements d (P.map Complex.ofRealHom) := by
      refine ⟨by rw [Polynomial.natDegree_map, hdeg], ?_, ?_, ?_, ?_⟩
      · unfold QAlgorithms.HasParity
        have : (P.map Complex.ofRealHom).comp (-Polynomial.X)
            = (P.comp (-Polynomial.X)).map Complex.ofRealHom := by
          rw [Polynomial.map_comp]; simp
        rw [this, hodd, hd.neg_one_pow]; simp
      · intro x hx; rw [evalC, Complex.norm_real, Real.norm_eq_abs]; exact hle x hx
      · intro x hx; rw [evalC, Complex.norm_real, Real.norm_eq_abs]; exact hge x hx
      · intro he; exact absurd he (Nat.not_even_iff_odd.mpr hd)
    obtain ⟨Φ, hΦ, -, -⟩ := QSVT19.Main.corollary_8 d hd1 _ hreq
    refine ⟨alt true (List.ofFn Φ ++ [0]), ?_, ?_, ?_⟩
    · obtain ⟨h1, h2⟩ := alt_count true (List.ofFn Φ ++ [0])
      rw [h1, h2]; simp only [if_true, List.length_append, List.length_ofFn, List.length_singleton]
      obtain ⟨k, rfl⟩ := hd; omega
    · obtain ⟨h1, -⟩ := alt_count true (List.ofFn Φ ++ [0])
      rw [h1]; simp only [if_true, List.length_append, List.length_ofFn, List.length_singleton]
      have : 2 * ((d + 1 + 1) / 2) = d + 1 := by obtain ⟨k, rfl⟩ := hd; omega
      calc (2 * (((d + 1 + 1) / 2 : ℕ) : ℝ)) = ((2 * ((d + 1 + 1) / 2) : ℕ) : ℝ) := by push_cast; ring
        _ = (d : ℝ) + 1 := by rw [this]; push_cast; ring
        _ ≤ _ := hbound
    · intro ς hς0 hς1
      have hx : ς ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith, hς1⟩
      refine ⟨P.eval ς, ?_, ?_⟩
      · rw [qsp_link d hd Φ ς hx, hΦ ς hx, evalC]
      · intro hδ
        exact ⟨happrox ς ⟨hδ, hς1⟩, (le_abs_self _).trans (hle ς hx)⟩
  · refine ⟨[], by simp, by
      simp only [List.filter_nil, List.length_nil, Nat.cast_zero, mul_zero]
      exact mul_nonneg hc.le (div_pos hL h2).le, ?_⟩
    intro ς hς0 hς1
    refine ⟨ς, by simp [Uop], fun hδ => ⟨by linarith, hς1⟩⟩


lemma callsA_progOf (l : List (Bool × ℝ)) :
    (progOf l).callsA = 2 * (l.filter (·.1)).length := by
  induction l with
  | nil => simp [progOf, RotationProgram.callsA]
  | cons x l ih =>
    have : progOf (x :: l) = pairProg x.1 x.2 ++ progOf l := by simp [progOf]
    rw [this, RotationProgram.callsA, List.countP_append]
    rw [RotationProgram.callsA] at ih
    rw [ih]
    rcases x with ⟨b, φ⟩
    cases b <;> simp [pairProg, List.filter_cons] <;> omega

lemma callsB_progOf (l : List (Bool × ℝ)) :
    (progOf l).callsB = 2 * (l.filter (!·.1)).length := by
  induction l with
  | nil => simp [progOf, RotationProgram.callsB]
  | cons x l ih =>
    have : progOf (x :: l) = pairProg x.1 x.2 ++ progOf l := by simp [progOf]
    rw [this, RotationProgram.callsB, List.countP_append]
    rw [RotationProgram.callsB] at ih
    rw [ih]
    rcases x with ⟨b, φ⟩
    cases b <;> simp [pairProg, List.filter_cons] <;> omega

lemma gates_progOf (l : List (Bool × ℝ)) : (progOf l).gates = l.length := by
  induction l with
  | nil => simp [progOf, RotationProgram.gates]
  | cons x l ih =>
    have : progOf (x :: l) = pairProg x.1 x.2 ++ progOf l := by simp [progOf]
    rw [this, RotationProgram.gates, List.countP_append]
    rw [RotationProgram.gates] at ih
    rw [ih]
    rcases x with ⟨b, φ⟩
    cases b <;> simp [pairProg] <;> omega

lemma filter_len (l : List (Bool × ℝ)) :
    l.length = (l.filter (·.1)).length + (l.filter (!·.1)).length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rcases x with ⟨b, φ⟩
    cases b <;> simp [List.filter_cons] <;> omega

lemma gate_unitary (φ : ℝ) :
    (!![Complex.exp (-(φ : ℂ) * Complex.I), 0; 0, Complex.exp ((φ : ℂ) * Complex.I)] :
      Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, ← Complex.exp_conj,
      ← Complex.exp_add]


section Bridge
open scoped InnerProductSpace
open Matrix
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma Fop_apply (P : H →L[ℂ] H) (φ : ℝ) (x : H) :
    Fop P φ x = Complex.exp (-(φ : ℂ) * Complex.I) • (x - P x) +
      Complex.exp ((φ : ℂ) * Complex.I) • P x := by
  simp [Fop, Algebra.algebraMap_eq_smul_one]

lemma Fopm_mulVec (Pm : Matrix (Fin 2) (Fin 2) ℂ) (φ : ℝ) (z : Fin 2 → ℂ) :
    Fop Pm φ *ᵥ z = Complex.exp (-(φ : ℂ) * Complex.I) • (z - Pm *ᵥ z) +
      Complex.exp ((φ : ℂ) * Complex.I) • (Pm *ᵥ z) := by
  simp [Fop, Algebra.algebraMap_eq_smul_one, Matrix.add_mulVec, Matrix.sub_mulVec,
    Matrix.smul_mulVec]

/-- `z ↦ z₀ v + z₁ u`. -/
def emb (v u : H) : (Fin 2 → ℂ) →ₗ[ℂ] H where
  toFun z := z 0 • v + z 1 • u
  map_add' z z' := by simp [add_smul]; abel
  map_smul' c z := by simp [smul_add, mul_smul]

lemma Fop_emb (v u : H) (P : H →L[ℂ] H) (Pm : Matrix (Fin 2) (Fin 2) ℂ)
    (h : ∀ z, P (emb v u z) = emb v u (Pm *ᵥ z)) (φ : ℝ) (z : Fin 2 → ℂ) :
    Fop P φ (emb v u z) = emb v u (Fop Pm φ *ᵥ z) := by
  rw [Fop_apply, Fopm_mulVec, map_add, map_smul, map_smul, map_sub, h]

lemma Uop_emb (v u : H) (PA PB : H →L[ℂ] H) (PAm PBm : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : ∀ z, PA (emb v u z) = emb v u (PAm *ᵥ z))
    (hB : ∀ z, PB (emb v u z) = emb v u (PBm *ᵥ z)) (l : List (Bool × ℝ)) (z : Fin 2 → ℂ) :
    Uop PA PB 1 l (emb v u z) = emb v u (Uop PAm PBm 1 l *ᵥ z) := by
  induction l generalizing z with
  | nil => simp [Uop]
  | cons x l ih =>
    simp only [Uop, ContinuousLinearMap.mul_apply, ← Matrix.mulVec_mulVec]
    rw [← ih]
    congr 1
    cases x.1
    · exact Fop_emb v u PB PBm hB _ z
    · exact Fop_emb v u PA PAm hA _ z

/-- Invariance of a subspace under the phase product. -/
lemma Uop_mem (S : Submodule ℂ H) (PA PB : H →L[ℂ] H) (hA : ∀ x ∈ S, PA x ∈ S)
    (hB : ∀ x ∈ S, PB x ∈ S) (l : List (Bool × ℝ)) (x : H) (hx : x ∈ S) :
    Uop PA PB 1 l x ∈ S := by
  induction l generalizing x with
  | nil => simpa [Uop] using hx
  | cons y l ih =>
    simp only [Uop, ContinuousLinearMap.mul_apply]
    apply ih
    rw [Fop_apply]
    have hP : ∀ x ∈ S, (if y.1 then PA else PB) x ∈ S := by
      intro x hx; cases y.1 <;> simp [hA x hx, hB x hx]
    exact S.add_mem (S.smul_mem _ (S.sub_mem hx (hP x hx))) (S.smul_mem _ (hP x hx))

/-- The auxiliary unit vector of a block. -/
lemma exists_u (v w : H) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (ς : ℝ) (hς : ⟪w, v⟫_ℂ = ς) :
    ∃ u : H, w = (ς : ℂ) • v + (Real.sqrt (1 - ς ^ 2) : ℂ) • u ∧ ⟪v, u⟫_ℂ = 0 ∧
      ⟪w, u⟫_ℂ = Real.sqrt (1 - ς ^ 2) ∧ u ∈ Submodule.span ℂ {v, w} := by
  set s := Real.sqrt (1 - ς ^ 2) with hs
  have hvv : ⟪v, v⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hv]; simp
  have hww : ⟪w, w⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hw]; simp
  have hvw : ⟪v, w⟫_ℂ = ς := by rw [← inner_conj_symm, hς]; simp
  have hς1 : ς ^ 2 ≤ 1 := by
    have := norm_inner_le_norm (𝕜 := ℂ) w v
    rw [hς, hv, hw, Complex.norm_real, Real.norm_eq_abs] at this
    nlinarith [abs_nonneg ς, sq_abs ς]
  -- `‖w - ς v‖² = 1 - ς²`
  have hd : ⟪w - (ς : ℂ) • v, w - (ς : ℂ) • v⟫_ℂ = ((1 - ς ^ 2 : ℝ) : ℂ) := by
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hvv, hww,
      hvw, hς, Complex.conj_ofReal]
    push_cast; ring
  have hs2 : s ^ 2 = 1 - ς ^ 2 := Real.sq_sqrt (by linarith)
  have hmem : w - (ς : ℂ) • v ∈ Submodule.span ℂ {v, w} :=
    Submodule.sub_mem _ (Submodule.subset_span (by simp))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  by_cases hs0 : s = 0
  · refine ⟨0, ?_, by simp, by simp [hs0], Submodule.zero_mem _⟩
    have : w - (ς : ℂ) • v = 0 := by
      rw [← inner_self_eq_zero (𝕜 := ℂ), hd, ← hs2, hs0]; simp
    rw [hs0]; simp only [Complex.ofReal_zero, zero_smul, add_zero]
    exact sub_eq_zero.mp this
  · refine ⟨((s : ℂ)⁻¹) • (w - (ς : ℂ) • v), ?_, ?_, ?_, Submodule.smul_mem _ _ hmem⟩
    · rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast hs0), one_smul]; abel
    · rw [inner_smul_right, inner_sub_right, inner_smul_right, hvw, hvv]; ring
    · rw [inner_smul_right, inner_sub_right, inner_smul_right, hww, hς]
      have : ((1 : ℂ) - (ς : ℂ) * ς) = (s : ℂ) * s := by
        have : ((s ^ 2 : ℝ) : ℂ) = ((1 - ς ^ 2 : ℝ) : ℂ) := by rw [hs2]
        push_cast at this; linear_combination -this
      rw [this]; field_simp


lemma ketBra_apply (y x z : H) : ketBra y x z = ⟪x, z⟫_ℂ • y := by
  simp [ketBra]

lemma sum_identity {PA PB : H →L[ℂ] H} (J : JordanDecomposition PA PB) (U : H →L[ℂ] H)
    (hU : ∀ j, ∀ x ∈ J.S j, U x ∈ J.S j) :
    PB * U * PA = ∑ j, ⟪J.w j, U (J.v j)⟫_ℂ • ketBra (J.w j) (J.v j) := by
  have hvS : ∀ j, J.v j ∈ J.S j := fun j => by
    rw [J.span_v j]; exact Submodule.subset_span (by simp)
  ext x
  have hx : x ∈ ⨆ j, J.S j := by rw [J.total]; trivial
  refine Submodule.iSup_induction J.S
    (motive := fun x => (PB * U * PA) x =
      (∑ j, ⟪J.w j, U (J.v j)⟫_ℂ • ketBra (J.w j) (J.v j)) x) hx ?_ ?_ ?_
  · intro i x hx
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, ketBra_apply]
    rw [J.act_A i x hx, map_smul, map_smul, J.act_B i _ (hU i _ (hvS i))]
    rw [Finset.sum_eq_single i]
    · rw [smul_smul, smul_smul, mul_comm]
    · intro j _ hji
      rw [(J.orthogonal j i hji).inner_eq (hvS j) hx]; simp
    · simp
  · simp
  · intro x y hx hy; rw [map_add, map_add, hx, hy]

lemma block_value {PA PB : H →L[ℂ] H} (J : JordanDecomposition PA PB) (j : J.idx)
    (hv : ‖J.v j‖ = 1) (hw : ‖J.w j‖ = 1) (l : List (Bool × ℝ)) :
    let ς := J.sv j
    let s := Real.sqrt (1 - ς ^ 2)
    let PAm : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]
    let PBm : Matrix (Fin 2) (Fin 2) ℂ := !![(ς : ℂ) ^ 2, ς * s; ς * s, (s : ℂ) ^ 2]
    let M := Uop PAm PBm 1 l
    ς ≤ 1 ∧ ⟪J.w j, Uop PA PB 1 l (J.v j)⟫_ℂ = (ς : ℂ) * M 0 0 + (s : ℂ) * M 1 0 := by
  intro ς s PAm PBm M
  set v := J.v j with hvdef
  set w := J.w j with hwdef
  have hsdef : Real.sqrt (1 - ς ^ 2) = s := rfl
  have hς : ⟪w, v⟫_ℂ = ς := J.overlap j
  have hς1 : ς ≤ 1 := by
    have := norm_inner_le_norm (𝕜 := ℂ) w v
    rw [hς, hv, hw, Complex.norm_real, Real.norm_eq_abs] at this
    linarith [le_abs_self ς]
  obtain ⟨u, hwd, hvu, hwu, huS⟩ := exists_u v w hv hw ς hς
  rw [hsdef] at hwd hwu
  have hvv : ⟪v, v⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hv]; simp
  have hvS : v ∈ J.S j := by rw [J.span_v j]; exact Submodule.subset_span (Set.mem_insert _ _)
  have hwS : w ∈ J.S j := by rw [J.span_w j]; exact Submodule.subset_span (Set.mem_insert _ _)
  have huS' : u ∈ J.S j := by
    refine Submodule.span_le.mpr ?_ huS
    intro y hy; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl <;> assumption
  have hembS : ∀ z, emb v u z ∈ J.S j := fun z =>
    (J.S j).add_mem ((J.S j).smul_mem _ hvS) ((J.S j).smul_mem _ huS')
  have hA : ∀ z, PA (emb v u z) = emb v u (PAm *ᵥ z) := by
    intro z
    rw [J.act_A j _ (hembS z), ← hvdef]
    simp [emb, PAm, hv, hvu, dotProduct, Fin.sum_univ_two]
  have hB : ∀ z, PB (emb v u z) = emb v u (PBm *ᵥ z) := by
    intro z
    rw [J.act_B j _ (hembS z), ← hwdef]
    have hc : ⟪w, emb v u z⟫_ℂ = z 0 * ς + z 1 * s := by
      simp [emb, inner_add_right, inner_smul_right, hς, hwu]
    rw [hc]
    conv_lhs => rw [hwd]
    simp only [emb, PBm, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    simp only [smul_add, smul_smul, add_smul]
    have e1 : (z 0 * ς + z 1 * s) * ς = (ς : ℂ) ^ 2 * z 0 + ς * s * z 1 := by ring
    have e2 : (z 0 * ς + z 1 * s) * s = ς * s * z 0 + (s : ℂ) ^ 2 * z 1 := by ring
    rw [e1, e2, add_smul, add_smul]
  have hv1 : emb v u ![1, 0] = v := by simp [emb]
  have hU := Uop_emb v u PA PB PAm PBm hA hB l ![1, 0]
  rw [hv1] at hU
  refine ⟨hς1, ?_⟩
  rw [hU]
  simp [emb, inner_add_right, inner_smul_right, hς, hwu, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]
  ring

end Bridge


/-- BRIDGE: unitarity of the phase product, and the Jordan-block reduction. -/
lemma bridge {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (PA PB : H →L[ℂ] H) (hA : IsHermitianProjector PA) (hB : IsHermitianProjector PB)
    (l : List (Bool × ℝ)) (ε δ : ℝ) (hδ : 0 < δ)
    (hcore : ∀ ς : ℝ, 0 ≤ ς → ς ≤ 1 →
        let s := Real.sqrt (1 - ς ^ 2)
        let PA : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]
        let PB : Matrix (Fin 2) (Fin 2) ℂ := !![(ς : ℂ) ^ 2, ς * s; ς * s, (s : ℂ) ^ 2]
        let M := Uop PA PB 1 l
        ∃ r : ℝ, ((ς : ℂ) * M 0 0 + (s : ℂ) * M 1 0 = r) ∧ (δ ≤ ς → 1 - ε ≤ r ∧ r ≤ 1)) :
    ∀ J : JordanDecomposition PA PB, IsRotationUnitary J ε δ (Uop PA PB 1 l) := by
  intro J
  set U := Uop PA PB 1 l with hUdef
  have hUu : U ∈ unitary (H →L[ℂ] H) := Uop_unitary PA PB hA.2 hB.2 hA.1 hB.1 1 l
  have hvS : ∀ j, J.v j ∈ J.S j := fun j => by
    rw [J.span_v j]; exact Submodule.subset_span (Set.mem_insert _ _)
  have hwS : ∀ j, J.w j ∈ J.S j := fun j => by
    rw [J.span_w j]; exact Submodule.subset_span (Set.mem_insert _ _)
  have hinv : ∀ j, ∀ x ∈ J.S j, U x ∈ J.S j := fun j x hx =>
    Uop_mem (J.S j) PA PB (fun y hy => by rw [J.act_A j y hy]; exact (J.S j).smul_mem _ (hvS j))
      (fun y hy => by rw [J.act_B j y hy]; exact (J.S j).smul_mem _ (hwS j)) l x hx
  have hj : ∀ j, ∃ r : ℝ, ⟪J.w j, U (J.v j)⟫_ℂ = r ∧
      (δ ≤ J.sv j → r ∈ Set.Icc (1 - ε) 1) ∧ (J.sv j < δ → r ∈ Set.Icc (-1) 1) := by
    intro j
    have hvw : (‖J.v j‖ = 1 ∨ J.v j = 0) ∧ (‖J.w j‖ = 1 ∨ J.w j = 0) := by
      rcases J.dim j with h | h
      · obtain ⟨h1, h2⟩ := J.one_dim j h
        exact ⟨h1.imp (fun h => h.1) (fun h => h.1), h2.imp (fun h => h.1) (fun h => h.1)⟩
      · obtain ⟨a, -, -, b, -⟩ := J.two_dim j h
        exact ⟨Or.inl a, Or.inl b⟩
    by_cases hnd : ‖J.v j‖ = 1 ∧ ‖J.w j‖ = 1
    · obtain ⟨hς1, hval⟩ := block_value J j hnd.1 hnd.2 l
      obtain ⟨r, hr, hrb⟩ := hcore (J.sv j) (J.sv_nonneg j) hς1
      have hval' : ⟪J.w j, U (J.v j)⟫_ℂ = r := hval.trans hr
      refine ⟨r, hval', fun h => hrb h, fun _ => ?_⟩
      have : ‖⟪J.w j, U (J.v j)⟫_ℂ‖ ≤ 1 := by
        calc _ ≤ ‖J.w j‖ * ‖U (J.v j)‖ := norm_inner_le_norm _ _
          _ = 1 := by rw [ContinuousLinearMap.norm_map_of_mem_unitary hUu, hnd.1, hnd.2]; ring
      rw [hval', Complex.norm_real, Real.norm_eq_abs] at this
      exact abs_le.mp this
    · have hzero : ⟪J.w j, U (J.v j)⟫_ℂ = 0 ∧ J.sv j = 0 := by
        have hov := J.overlap j
        rcases hvw with ⟨hv | hv, hw | hw⟩
        · exact absurd ⟨hv, hw⟩ hnd
        · rw [hw, inner_zero_left] at hov ⊢; exact ⟨rfl, by exact_mod_cast hov.symm⟩
        · rw [hv, inner_zero_right] at hov; rw [hv, map_zero, inner_zero_right]
          exact ⟨rfl, by exact_mod_cast hov.symm⟩
        · rw [hw, inner_zero_left] at hov ⊢; exact ⟨rfl, by exact_mod_cast hov.symm⟩
      refine ⟨0, by rw [hzero.1]; simp, fun h => by linarith [hzero.2], fun _ => by norm_num⟩
  choose r hr using hj
  refine ⟨hUu, r, ?_, fun j => (hr j).2⟩
  rw [sum_identity J U hinv]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [(hr j).1]

theorem theorem_3_9 : ∃ (c : ℝ) (prog : ℝ → ℝ → RotationProgram), 0 < c ∧
    IsRotationFamily c prog := by
  classical
  obtain ⟨c, hc, h⟩ := core_phases
  refine ⟨c, fun ε δ => if H : 0 < ε ∧ ε < 1 ∧ 0 < δ ∧ δ < 1 then
    progOf (Classical.choose (h ε δ H.1 H.2.1 H.2.2.1 H.2.2.2)) else [], hc, ?_⟩
  intro ε δ h0 h1 h2 h3
  have H : 0 < ε ∧ ε < 1 ∧ 0 < δ ∧ δ < 1 := ⟨h0, h1, h2, h3⟩
  simp only [dif_pos H]
  obtain ⟨hlen, hbound, hspec⟩ := Classical.choose_spec (h ε δ h0 h1 h2 h3)
  set l := Classical.choose (h ε δ h0 h1 h2 h3)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [progOf, List.mem_flatMap, pairProg] at hg
    obtain ⟨x, -, hx⟩ := hg
    have hg' : g = !![Complex.exp (-(x.2 : ℂ) * Complex.I), 0; 0, Complex.exp ((x.2 : ℂ) * Complex.I)] := by
      rcases x with ⟨b, φ⟩
      cases b <;> simp [pairProg] at hx ⊢ <;> tauto
    rw [hg']
    exact gate_unitary x.2
  · rw [callsA_progOf, callsB_progOf, hlen]
  · rw [gates_progOf, callsA_progOf, filter_len l, ← hlen]; ring
  · rw [callsA_progOf]; exact_mod_cast hbound
  · intro H' _ _ _ PA PB hA hB
    have hA' : PA * PA = PA := hA.2
    have hB' : PB * PB = PB := hB.2
    rw [prog_op PA PB hA' hB' l]
    have hJ := bridge PA PB hA hB l ε δ h2 hspec
    have hu : ∀ s, Uop PA PB s l ∈ unitary (H' →L[ℂ] H') := fun s =>
      Uop_unitary PA PB hA' hB' hA.1 hB.1 s l
    refine ⟨by simp, by simpa using hu 1, ?_⟩
    intro J
    simpa using hJ J

end TightPQRepetition.Main

open TightPQRepetition.Main in
theorem solution : ∃ (c : ℝ) (prog : ℝ → ℝ → RotationProgram), 0 < c ∧
    IsRotationFamily c prog :=
  TightPQRepetition.Main.theorem_3_9
