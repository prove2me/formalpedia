-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P08.theorem3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T02:03:23.930126+00:00
-- url     : https://prove2.me/submissions/318c7191-ebbc-4fa9-8dd6-36a81080a880

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

set_option maxHeartbeats 800000 in
private lemma choi_tests (t lam : Bloch)
    (h : (idTensorSuperop (canonical t lam) bellDensity).PosSemidef)
    (hp : (partialTransposeFirst (idTensorSuperop (canonical t lam) bellDensity)).PosSemidef) :
    (0 ≤ 1 + lam 2 + (lam 0 + lam 1)) ∧
    (0 ≤ 1 + lam 2 - (lam 0 + lam 1)) ∧
    (0 ≤ 1 - lam 2 + (lam 0 - lam 1)) ∧
    (0 ≤ 1 - lam 2 - (lam 0 - lam 1)) ∧
    (0 ≤ 1 + lam 2 + (lam 0 - lam 1)) ∧
    (0 ≤ 1 + lam 2 - (lam 0 - lam 1)) ∧
    (0 ≤ 1 - lam 2 + (lam 0 + lam 1)) ∧
    (0 ≤ 1 - lam 2 - (lam 0 + lam 1)) := by
  have h1 := quadratic_nonneg h (testVector false 1)
  have h2 := quadratic_nonneg h (testVector false (-1))
  have h3 := quadratic_nonneg h (testVector true 1)
  have h4 := quadratic_nonneg h (testVector true (-1))
  have h5 := quadratic_nonneg hp (testVector false 1)
  have h6 := quadratic_nonneg hp (testVector false (-1))
  have h7 := quadratic_nonneg hp (testVector true 1)
  have h8 := quadratic_nonneg hp (testVector true (-1))
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_succ,
    Fintype.sum_bool] at h1 h2 h3 h4 h5 h6 h7 h8
  norm_num [testVector] at h1 h2 h3 h4 h5 h6 h7 h8
  norm_num [Matrix.mul_apply, Matrix.sum_apply, Finset.sum_apply, idTensorSuperop, canonical,
    blochAffineMap, bellDensity, testVector, partialTransposeFirst, sigma,
    pauliX, pauliY, pauliZ, Matrix.trace, Matrix.diag, Matrix.diagonal,
    Matrix.vecMulVec, Fintype.sum_prod_type, Fin.sum_univ_succ, Complex.ext_iff] at h1 h2 h3 h4 h5 h6 h7 h8
  constructor
  · linarith only [h1]
  constructor
  · linarith only [h2]
  constructor
  · linarith only [h3]
  constructor
  · linarith only [h4]
  constructor
  · linarith only [h5]
  constructor
  · linarith only [h6]
  constructor
  · linarith only [h7]
  linarith only [h8]

theorem solution (t lam : Bloch) (hPhi : EBT (canonical t lam)) :
    ∑ j, |lam j| ≤ 1 := by
  have hs := hPhi.2 2 (by norm_num) bellDensity bell_density
  obtain ⟨h,hp⟩ := sep_positive hs
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := choi_tests t lam h hp
  rw [Fin.sum_univ_three]
  rcases le_total 0 (lam 0) with ha | ha <;>
    rcases le_total 0 (lam 1) with hb | hb <;>
    rcases le_total 0 (lam 2) with hc | hc <;>
    simp only [abs_of_nonneg, abs_of_nonpos, ha, hb, hc] <;>
    linarith only [h1,h2,h3,h4,h5,h6,h7,h8]
