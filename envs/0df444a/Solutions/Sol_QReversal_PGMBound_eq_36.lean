-- Prove2me | solution 1 for QReversal.PGMBound.eq_36
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-19T22:02:50.590466+00:00
-- url     : https://prove2.me/submissions/7e7ef81f-d99c-4d09-a173-64905be31c72

import Mathlib
import Definitions.Def_QReversal_PGMBound_Setting

open Matrix PeresTerno
open scoped MatrixOrder ComplexOrder

namespace QReversal.PGMBound

lemma e36_term {J O : Type*} [Fintype J] [DecidableEq J] [Fintype O] [DecidableEq O]
    (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ) (hl : ∀ i j, 0 ≤ lam i j)
    (i : O) (j : J) :
    classicKraus lam v (i, j) * rho p * (classicKraus lam v (i, j))ᴴ
      = ((p j : ℂ) * (lam i j : ℂ)) • vecMulVec (v i j) (star (v i j)) := by
  have hs : (Real.sqrt (lam i j) : ℂ) * (Real.sqrt (lam i j) : ℂ) = (lam i j : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hl i j)]
  ext a b
  simp [classicKraus, rho, Matrix.mul_apply, vecMulVec_apply, Pi.single_apply, diagonal_apply]
  linear_combination (p j * v i j a * (starRingEnd ℂ) (v i j b)) * hs

lemma e36_sqrt {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) :
    CFC.sqrt (rho p) = Matrix.diagonal (fun j => (Real.sqrt (p j) : ℂ)) := by
  apply CFC.sqrt_unique
  · rw [rho, diagonal_mul_diagonal]
    congr 1; funext j
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hp j)]
  · rw [nonneg_iff_posSemidef]
    exact PosSemidef.diagonal (fun j => Complex.zero_le_real.mpr (Real.sqrt_nonneg _))

lemma e36_rhoOut {J O : Type*} [Fintype J] [DecidableEq J] [Fintype O] [DecidableEq O]
    (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ) (hl : ∀ i j, 0 ≤ lam i j) :
    rhoOut p lam v = ∑ j, weightedState p lam v j := by
  rw [rhoOut, krausUpdate, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [weightedState, rhoHat, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [e36_term p lam v hl, smul_smul]

lemma e36_left {J O : Type*} [Fintype J] [DecidableEq J] [Fintype O] [DecidableEq O]
    (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ) (i : O) (j : J) :
    Matrix.diagonal (fun j => (Real.sqrt (p j) : ℂ)) * (classicKraus lam v (i, j))ᴴ
      = (Real.sqrt (p j) * Real.sqrt (lam i j) : ℂ) •
        vecMulVec (Pi.single j 1) (star (v i j)) := by
  ext a b
  simp [classicKraus, Matrix.mul_apply, vecMulVec_apply,
    Pi.single_apply, diagonal_apply]
  split_ifs with h
  · subst h; ring
  · rfl

theorem eq_36_main {J O : Type*} [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O]
    (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hp : IsProbability p) (hs : IsSpectralData lam v)
    (_hfull : (rhoOut p lam v).PosDef) :
    rhoOut p lam v = ∑ j, weightedState p lam v j ∧
    ∀ i j, reversal (classicKraus lam v) (rho p) (i, j) =
      ((Real.sqrt (p j) * Real.sqrt (lam i j) : ℂ) •
        vecMulVec (Pi.single j 1) (star (v i j))) *
        QReversal.NearOpt.invSqrt (∑ k, weightedState p lam v k) := by
  have h1 := e36_rhoOut p lam v hs.1
  refine ⟨h1, fun i j => ?_⟩
  have h2 : krausUpdate (classicKraus lam v) (rho p) = rhoOut p lam v := rfl
  rw [reversal, h2, h1, e36_sqrt p hp.1, e36_left]

end QReversal.PGMBound

theorem solution {J O : Type*} [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O]
    (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hp : QReversal.PGMBound.IsProbability p) (hs : QReversal.PGMBound.IsSpectralData lam v)
    (hfull : (QReversal.PGMBound.rhoOut p lam v).PosDef) :
    QReversal.PGMBound.rhoOut p lam v = ∑ j, QReversal.PGMBound.weightedState p lam v j ∧
    ∀ i j, QReversal.PGMBound.reversal (QReversal.PGMBound.classicKraus lam v)
        (QReversal.PGMBound.rho p) (i, j) =
      ((Real.sqrt (p j) * Real.sqrt (lam i j) : ℂ) •
        vecMulVec (Pi.single j 1) (star (v i j))) *
        QReversal.NearOpt.invSqrt (∑ k, QReversal.PGMBound.weightedState p lam v k) :=
  QReversal.PGMBound.eq_36_main p lam v hp hs hfull
