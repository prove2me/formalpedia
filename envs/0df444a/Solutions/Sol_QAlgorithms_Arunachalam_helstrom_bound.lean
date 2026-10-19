-- Prove2me | solution 1 for QAlgorithms.Arunachalam.helstrom_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T09:26:22.005287+00:00
-- url     : https://prove2.me/submissions/b67b3056-6cae-453e-8696-c1f74fae3f0e

import Definitions.Def_QAlgorithms_Defs_BooleanFourier
import Mathlib.Analysis.Matrix.Order

set_option autoImplicit false
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder
open Matrix QAlgorithms

private lemma act_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ)
    (x : EuclideanSpace ℂ ι) : act (A * B) x = act A (act B x) := by
  ext i
  exact congrFun (Matrix.mulVec_mulVec x A B).symm i

private lemma inner_act {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ)
    (x y : EuclideanSpace ℂ ι) :
    inner ℂ (act A x) y = inner ℂ x (act Aᴴ y) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, act]
  rw [Matrix.star_mulVec, dotProduct_comm, ← Matrix.dotProduct_mulVec, dotProduct_comm]

private lemma effect_inner {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ)
    (x : EuclideanSpace ℂ ι) :
    effectProb A (pureDensity x) = (inner ℂ x (act A x)).re := by
  unfold effectProb
  congr 1
  simp only [pureDensity, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.of_apply, EuclideanSpace.inner_eq_star_dotProduct, act,
    Matrix.mulVec, dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  change A i j * (x j * star (x i)) = (A i j * x j) * star (x i)
  ring

private lemma effect_sqrt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.PosSemidef) :
    ∃ S : Matrix ι ι ℂ, (∀ x y : EuclideanSpace ℂ ι,
      inner ℂ (act S x) (act S y) = inner ℂ x (act A y)) ∧
      ∀ x : EuclideanSpace ℂ ι, ‖act S x‖ ^ 2 = effectProb A (pureDensity x) := by
  let S := CFC.sqrt A
  have hS : S.PosSemidef := (CFC.sqrt_nonneg A).posSemidef
  have hsq : S * S = A := by simpa only [pow_two] using CFC.sq_sqrt A hA.nonneg
  have hid (x y : EuclideanSpace ℂ ι) :
      inner ℂ (act S x) (act S y) = inner ℂ x (act A y) := by
    rw [inner_act, hS.isHermitian.eq, ← act_mul, hsq]
  refine ⟨S, hid, fun x => ?_⟩
  rw [effect_inner, ← hid]
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) (act S x)).symm

private lemma four_norms (a b c d r : ℝ) (hr : 0 ≤ r)
    (habcd : r ≤ a*b+c*d) (ha : a^2+c^2=1) (hb : b^2+d^2=1) :
    r^2 + (a^2-b^2)^2 ≤ 1 := by
  have hr2 : r^2 ≤ (a*b+c*d)^2 := by nlinarith
  have h1 := congrArg (fun t : ℝ => t * a^2) ha
  have h2 := congrArg (fun t : ℝ => t * b^2) hb
  have h3 := congrArg (fun t : ℝ => t * b^2) ha
  have h4 := congrArg (fun t : ℝ => t * d^2) ha
  nlinarith [sq_nonneg (a*c-b*d)]

private lemma act_add {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ)
    (x : EuclideanSpace ℂ ι) : act (A+B) x = act A x + act B x := by
  ext i
  exact congrFun (Matrix.add_mulVec A B x) i

private lemma act_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : EuclideanSpace ℂ ι) : act 1 x = x := by
  ext i
  exact congrFun (Matrix.one_mulVec x) i

private lemma two_outcomes {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : Bool → EuclideanSpace ℂ ι) (hψ : ∀ b, IsState (ψ b))
    (M : Bool → Matrix ι ι ℂ) (hM : IsPOVM M) :
    ‖inner ℂ (ψ false) (ψ true)‖ ^ 2 +
      (2 * ensembleSuccess (fun _ => (1/2 : ℝ)) ψ M - 1)^2 ≤ 1 := by
  obtain ⟨S, hS, hSn⟩ := effect_sqrt (M false) (hM.1 false)
  obtain ⟨T, hT, hTn⟩ := effect_sqrt (M true) (hM.1 true)
  have hMsum : M false + M true = 1 := by
    simpa only [Fintype.sum_bool, add_comm] using hM.2
  have hsplit (x y : EuclideanSpace ℂ ι) :
      inner ℂ x (act (M false) y) + inner ℂ x (act (M true) y) = inner ℂ x y := by
    rw [← inner_add_right, ← act_add, hMsum, act_one]
  have hnorm (b : Bool) : ‖act S (ψ b)‖^2 + ‖act T (ψ b)‖^2 = 1 := by
    rw [hSn, hTn, effect_inner, effect_inner, ← Complex.add_re, hsplit]
    calc
      _ = ‖ψ b‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
      _ = 1 := by rw [hψ b]; norm_num

  have hr : ‖inner ℂ (ψ false) (ψ true)‖ ≤
      ‖act S (ψ false)‖ * ‖act S (ψ true)‖ +
        ‖act T (ψ false)‖ * ‖act T (ψ true)‖ := by
    calc
      _ = ‖inner ℂ (act S (ψ false)) (act S (ψ true)) +
          inner ℂ (act T (ψ false)) (act T (ψ true))‖ := by rw [hS, hT, hsplit]
      _ ≤ ‖inner ℂ (act S (ψ false)) (act S (ψ true))‖ +
          ‖inner ℂ (act T (ψ false)) (act T (ψ true))‖ := norm_add_le _ _
      _ ≤ _ := add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
  have hbound := four_norms ‖act S (ψ false)‖ ‖act S (ψ true)‖
    ‖act T (ψ false)‖ ‖act T (ψ true)‖ ‖inner ℂ (ψ false) (ψ true)‖
    (norm_nonneg _) hr (hnorm false) (hnorm true)
  have hsucc : 2 * ensembleSuccess (fun _ => (1/2 : ℝ)) ψ M - 1 =
      ‖act S (ψ false)‖^2 - ‖act S (ψ true)‖^2 := by
    simp only [ensembleSuccess, Fintype.sum_bool]
    rw [← hSn, ← hTn]
    nlinarith [hnorm true]
  rwa [hsucc]

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : Bool → EuclideanSpace ℂ ι) (hψ : ∀ b, IsState (ψ b))
    (M : Bool → Matrix ι ι ℂ) (hM : IsPOVM M) :
    ensembleSuccess (fun _ => (1 / 2 : ℝ)) ψ M ≤
        1 / 2 + 1 / 2 * Real.sqrt (1 - ‖inner ℂ (ψ false) (ψ true)‖ ^ 2) ∧
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 2 → 1 - δ ≤ ensembleSuccess (fun _ => (1 / 2 : ℝ)) ψ M →
        ‖inner ℂ (ψ false) (ψ true)‖ ≤ 2 * Real.sqrt (δ * (1 - δ)) := by
  have h := two_outcomes ψ hψ M hM
  have hrad : 0 ≤ 1 - ‖inner ℂ (ψ false) (ψ true)‖^2 := by nlinarith [sq_nonneg (2 * ensembleSuccess (fun _ => (1/2 : ℝ)) ψ M - 1)]
  have hs := Real.sq_sqrt hrad
  have hn := Real.sqrt_nonneg (1 - ‖inner ℂ (ψ false) (ψ true)‖^2)
  have hupper : ensembleSuccess (fun _ => (1/2 : ℝ)) ψ M ≤
      1/2+1/2*Real.sqrt (1-‖inner ℂ (ψ false) (ψ true)‖^2) := by
    nlinarith
  refine ⟨hupper, fun δ hδ hδhalf hsucc => ?_⟩
  have hd : 0 ≤ δ*(1-δ) := mul_nonneg hδ (by linarith)
  have hd2 := Real.sq_sqrt hd
  have hdn := Real.sqrt_nonneg (δ*(1-δ))
  have hprob : 0 ≤ 2 * ensembleSuccess (fun _ => (1/2 : ℝ)) ψ M - 1 := by linarith
  nlinarith [norm_nonneg (inner ℂ (ψ false) (ψ true))]
