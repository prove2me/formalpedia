-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P08.amplitudeDamping
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T02:13:17.253422+00:00
-- url     : https://prove2.me/submissions/563888cf-c849-4774-a4ea-bc1ef04c613c

import Definitions.Def_QAlgorithms_Defs_QubitBlochMaps
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P08_Model
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexOrder
open QAlgorithms QAlgorithms.Entanglement QAlgorithms.QubitChannels
open QAlgorithms.Papers.Independent.Independent1.P08

private lemma damping_apply (a : ℝ) (X : Matrix Bool Bool ℂ) (i j : Bool) :
    damping a X i j =
      if i then (if j then (a : ℂ)^2 * X true true else (a : ℂ)*X true false)
      else (if j then (a : ℂ)*X false true
        else X false false + (1-(a : ℂ)^2)*X true true) := by
  cases i <;> cases j <;>
    norm_num [damping, canonical, blochAffineMap, Matrix.mul_apply, Matrix.sum_apply,
      sigma, pauliX, pauliY, pauliZ, Matrix.trace, Matrix.diag, Matrix.diagonal,
      Fin.sum_univ_succ, Fintype.sum_bool] <;>
    ring_nf <;> norm_num [Complex.I_sq, Fin.ext_iff] <;> ring

private def K0 (a : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun b => if b then (a : ℂ) else 1

private def K1 (a : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.single false true (Real.sqrt (1-a^2) : ℂ)

private lemma damping_kraus (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (X : Matrix Bool Bool ℂ) :
    damping a X = K0 a * X * (K0 a)ᴴ + K1 a * X * (K1 a)ᴴ := by
  have hs : (Real.sqrt (1-a^2) : ℂ)^2 = 1-(a : ℂ)^2 := by
    exact_mod_cast Real.sq_sqrt (show 0 ≤ 1-a^2 by nlinarith)
  ext i j
  cases i <;> cases j <;>
    simp [damping_apply, K0, K1, Matrix.mul_apply, Matrix.diagonal,
      Matrix.conjTranspose_apply] <;>
    ring_nf
  all_goals rw [hs]; ring

private lemma lifted_sandwich {r : ℕ} (K : Matrix Bool Bool ℂ)
    (X : Matrix (Fin r × Bool) (Fin r × Bool) ℂ) :
    idTensorSuperop (conjSuperop K) X =
      Matrix.kronecker (1 : Matrix (Fin r) (Fin r) ℂ) K * X *
        (Matrix.kronecker (1 : Matrix (Fin r) (Fin r) ℂ) K)ᴴ := by
  simp only [Matrix.kronecker]
  rw [Matrix.conjTranspose_kronecker']
  ext p q
  simp [idTensorSuperop, conjSuperop, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.conjTranspose_apply, Matrix.one_apply]

private lemma damping_cpt (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) : CPT (damping a) := by
  constructor
  · intro X
    simp [Matrix.trace, Matrix.diag, damping_apply]
    ring
  · intro r X hX
    have he : idTensorSuperop (damping a) X =
        idTensorSuperop (conjSuperop (K0 a)) X +
          idTensorSuperop (conjSuperop (K1 a)) X := by
      ext p q
      exact congrFun (congrFun (damping_kraus a ha ha1 _) p.2) q.2
    rw [he, lifted_sandwich, lifted_sandwich]
    exact (hX.mul_mul_conjTranspose_same _).add (hX.mul_mul_conjTranspose_same _)

private def ground : Matrix Bool Bool ℂ := Matrix.single false false 1

private lemma ground_density : IsDensityMatrix ground := by
  have he : ground = Matrix.vecMulVec (fun b : Bool => if b then (0 : ℂ) else 1)
      (star (fun b : Bool => if b then (0 : ℂ) else 1)) := by
    ext i j; cases i <;> cases j <;> simp [ground, Matrix.vecMulVec]
  constructor
  · rw [he]; exact Matrix.posSemidef_vecMulVec_self_star _
  · simp [ground, Matrix.trace, Matrix.diag, Matrix.single_apply]

private lemma damping_zero_eb : EBT (damping 0) := by
  refine ⟨(damping_cpt 0 (by norm_num) (by norm_num)).1, ?_⟩
  intro r hr X hX
  let A : Matrix (Fin r) (Fin r) ℂ :=
    X.submatrix (fun i => (i,false)) (fun i => (i,false)) +
      X.submatrix (fun i => (i,true)) (fun i => (i,true))
  have hA : IsDensityMatrix A := by
    constructor
    · exact (hX.1.submatrix _).add (hX.1.submatrix _)
    · have ht := hX.2
      simpa [A, Matrix.trace, Matrix.diag, Fintype.sum_prod_type,
        Fintype.sum_bool, Finset.sum_add_distrib, add_comm] using ht
  refine ⟨1, fun _ => 1, fun _ => A, fun _ => ground,
    (by intro j; norm_num), (by simp), (fun _ => ⟨hA,ground_density⟩), ?_⟩
  ext p q
  rcases p with ⟨i,b⟩; rcases q with ⟨j,c⟩
  cases b <;> cases c <;>
    simp [idTensorSuperop, damping_apply, ground, A]

private lemma sep_positive {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    {X : Matrix (I × J) (I × J) ℂ} (h : IsSeparableDensity X) :
    X.PosSemidef ∧ (partialTransposeFirst X).PosSemidef := by
  classical
  obtain ⟨q,w,A,B,hw,_,hAB,rfl⟩ := h
  constructor
  · exact Matrix.posSemidef_sum _ fun j _ =>
      ((hAB j).1.1.kronecker (hAB j).2.1).smul (by exact_mod_cast hw j : (0 : ℂ) ≤ w j)
  · have he : partialTransposeFirst (∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j)) =
        ∑ j, (w j : ℂ) • Matrix.kronecker (A j)ᵀ (B j) := by
      ext p r
      simp [partialTransposeFirst, Matrix.sum_apply]
    rw [he]
    exact Matrix.posSemidef_sum _ fun j _ =>
      ((hAB j).1.1.transpose.kronecker (hAB j).2.1).smul
        (by exact_mod_cast hw j : (0 : ℂ) ≤ w j)

private def testVector (r : Bool) (s : ℂ) : Fin 2 × Bool → ℂ := fun p =>
  if p.2 = r then (if p.1 = 0 then 1 else 0) else (if p.1 = 1 then s else 0)

private def bellDensity : Matrix (Fin 2 × Bool) (Fin 2 × Bool) ℂ :=
  (1/2 : ℂ) • Matrix.vecMulVec (testVector false 1) (star (testVector false 1))

private lemma bell_density : IsDensityMatrix bellDensity := by
  constructor
  · exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by norm_num [Complex.nonneg_iff])
  · norm_num [bellDensity, Matrix.trace, Matrix.diag, Matrix.vecMulVec, testVector,
      Fintype.sum_prod_type, Fin.sum_univ_succ]

private lemma quadratic_nonneg {I : Type*} [Fintype I] {A : Matrix I I ℂ}
    (h : A.PosSemidef) (v : I → ℂ) :
    0 ≤ (star v ⬝ᵥ (A *ᵥ v)).re := by
  exact (Complex.nonneg_iff.mp (h.dotProduct_mulVec_nonneg v)).1

private lemma damping_eb_only_zero (a : ℝ) (ha : 0 ≤ a) (h : EBT (damping a)) : a = 0 := by
  have hp := (sep_positive (h.2 2 (by norm_num) bellDensity bell_density)).2
  have hn := quadratic_nonneg hp (testVector true (-(a : ℂ)))
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_succ,
    Fintype.sum_bool] at hn
  norm_num [testVector] at hn
  norm_num [partialTransposeFirst, idTensorSuperop, damping_apply, bellDensity,
    testVector, Matrix.vecMulVec, Complex.ext_iff, pow_two] at hn
  nlinarith [sq_nonneg (a^2)]

theorem solution :
    (∀ a : ℝ, 0 ≤ a → a ≤ 1 → CPT (damping a) ∧ (EBT (damping a) ↔ a = 0)) ∧
    ∀ eta : ℝ, 0 < eta → ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ 2*a+a^2 < eta ∧ ¬ EBT (damping a) := by
  constructor
  · intro a ha ha1
    refine ⟨damping_cpt a ha ha1, ⟨damping_eb_only_zero a ha, ?_⟩⟩
    rintro rfl; exact damping_zero_eb
  · intro eta heta
    let a := min (1/2 : ℝ) (eta/4)
    have ha : 0 < a := lt_min (by norm_num) (by positivity)
    have ha1 : a ≤ 1/2 := min_le_left _ _
    have hae : a ≤ eta/4 := min_le_right _ _
    refine ⟨a, ha, by linarith, ?_, ?_⟩
    · nlinarith
    · intro h
      exact ne_of_gt ha (damping_eb_only_zero a (le_of_lt ha) h)
