-- Prove2me | solution 1 for QReversal.PGMBound.eq_38
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-19T22:45:30.484869+00:00
-- url     : https://prove2.me/submissions/848289af-a2fc-441a-bb01-d55dea9e6aff

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

lemma e38_specpos {n : Type*} [Fintype n] [DecidableEq n] (R : Matrix n n ℂ) (h : R.PosDef)
    (x : ℝ) (hx : x ∈ spectrum ℝ R) : 0 < x := by
  have h0 : (0 : Matrix n n ℂ) ≤ R := by
    rw [Matrix.nonneg_iff_posSemidef]; exact h.posSemidef
  have h1 : 0 ≤ x := spectrum_nonneg_of_nonneg h0 hx
  have h2 : x ≠ 0 := by
    rintro rfl
    exact (spectrum.zero_notMem_iff ℝ).mpr h.isUnit hx
  exact lt_of_le_of_ne h1 (Ne.symm h2)

lemma e38_SRS {n : Type*} [Fintype n] [DecidableEq n] (R : Matrix n n ℂ) (h : R.PosDef) :
    QReversal.NearOpt.invSqrt R * R * QReversal.NearOpt.invSqrt R = 1 := by
  have hsa : IsSelfAdjoint R := h.isHermitian
  have hfin := finite_real_spectrum (A := R)
  unfold QReversal.NearOpt.invSqrt
  have hR : R = cfc (fun x : ℝ => x) R := (cfc_id' ℝ R).symm
  conv_lhs => arg 1; arg 2; rw [hR]
  rw [mul_assoc, ← cfc_mul _ _ R (hfin.continuousOn _) (hfin.continuousOn _),
    ← cfc_mul _ _ R (hfin.continuousOn _) (hfin.continuousOn _), ← cfc_const_one ℝ R]
  apply cfc_congr
  intro x hx
  have hx0 := e38_specpos R h x hx
  have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx0).ne'
  have := Real.mul_self_sqrt hx0.le
  field_simp
  linarith

lemma e38_sandwich {J O : Type*} [Fintype O] [Fintype J] (u : J → ℂ) (w x : O → ℂ) (y : J → ℂ)
    (S : Matrix O O ℂ) :
    vecMulVec u w * S * vecMulVec x y = (w ⬝ᵥ (S *ᵥ x)) • vecMulVec u y := by
  ext a b
  simp only [mul_apply, vecMulVec_apply, Matrix.smul_apply, dotProduct, mulVec, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

lemma e38_trace {O : Type*} [Fintype O] (S : Matrix O O ℂ) (u w : O → ℂ) :
    Matrix.trace (S * vecMulVec u w) = w ⬝ᵥ (S *ᵥ u) := by
  simp only [Matrix.trace, diag, mul_apply, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

lemma e38_star {O : Type*} [Fintype O] (S : Matrix O O ℂ) (hS : Sᴴ = S) (u w : O → ℂ) :
    star (star u ⬝ᵥ (S *ᵥ w)) = star w ⬝ᵥ (S *ᵥ u) := by
  conv_rhs => rw [← hS]
  simp only [dotProduct, mulVec, star_sum, star_mul', star_star, conjTranspose_apply,
    Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

lemma e38_diag {J : Type*} [Fintype J] [DecidableEq J] (M : Matrix J J ℂ) (j : J) :
    (M * Matrix.single j j (1:ℂ) * Mᴴ) j j = M j j * star (M j j) := by
  simp [mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, conjTranspose_apply]


lemma e38_tr4 {O : Type*} [Fintype O] (S : Matrix O O ℂ) (u w : O → ℂ) :
    Matrix.trace (S * vecMulVec u (star u) * S * vecMulVec w (star w)) =
      (star u ⬝ᵥ (S *ᵥ w)) * (star w ⬝ᵥ (S *ᵥ u)) := by
  rw [mul_assoc S, mul_assoc S, e38_sandwich, Matrix.mul_smul, trace_smul, e38_trace, smul_eq_mul]

lemma e38_K {J O : Type*} [Fintype J] [DecidableEq J] [Fintype O] [DecidableEq O]
    (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ) (hp : ∀ j, 0 ≤ p j)
    (a : O) (b : J) (c : O) (d : J) (j : J) :
    comp (reversal (classicKraus lam v) (rho p)) (classicKraus lam v) ((a, b), (c, d)) j j
      = ((Pi.single b (1:ℂ) : J → ℂ) j * (Pi.single d (1:ℂ) : J → ℂ) j) *
        (((Real.sqrt (p b) * Real.sqrt (lam a b) * Real.sqrt (lam c d) : ℝ) : ℂ) *
          (star (v a b) ⬝ᵥ (QReversal.NearOpt.invSqrt (rhoOut p lam v) *ᵥ v c d))) := by
  have hR : reversal (classicKraus lam v) (rho p) (a, b) =
      ((Real.sqrt (p b) * Real.sqrt (lam a b) : ℂ) •
        vecMulVec (Pi.single b 1) (star (v a b))) * QReversal.NearOpt.invSqrt (rhoOut p lam v) := by
    rw [reversal, e36_sqrt p hp, e36_left]; rfl
  have hA : classicKraus lam v (c, d) =
      (Real.sqrt (lam c d) : ℂ) • vecMulVec (v c d) (Pi.single d 1) := rfl
  simp only [comp]
  rw [hR, hA]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  rw [e38_sandwich]
  simp only [Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  push_cast; ring

lemma e38_diagj {J O : Type*} [Fintype J] [DecidableEq J] [Fintype O] [DecidableEq O]
    (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hp : ∀ j, 0 ≤ p j) (hs : IsSpectralData lam v) (j : J) :
    p j * (krausUpdate (comp (reversal (classicKraus lam v) (rho p)) (classicKraus lam v))
        (Matrix.single j j 1) j j).re =
      (Matrix.trace
        (QReversal.NearOpt.invSqrt (rhoOut p lam v) * weightedState p lam v j *
         QReversal.NearOpt.invSqrt (rhoOut p lam v) * weightedState p lam v j)).re := by
  set S := QReversal.NearOpt.invSqrt (rhoOut p lam v) with hSdef
  have hS : Sᴴ = S := (IsSelfAdjoint.cfc (f := fun x : ℝ => (Real.sqrt x)⁻¹)
    (a := rhoOut p lam v)).star_eq
  rw [← Complex.re_ofReal_mul]
  congr 1
  rw [krausUpdate, Matrix.sum_apply]
  simp only [e38_diag, Fintype.sum_prod_type, e38_K p lam v hp, ← hSdef]
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [weightedState, rhoHat, Finset.smul_sum, Matrix.mul_sum, Matrix.sum_mul,
    trace_sum, Matrix.smul_mul, Matrix.mul_smul, trace_smul, e38_tr4, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [star_mul', Complex.star_def, Complex.conj_ofReal, ← Complex.star_def, e38_star S hS]
  have hk : ((Real.sqrt (p j) * Real.sqrt (lam a j) * Real.sqrt (lam c j) : ℝ) : ℂ) *
      ((Real.sqrt (p j) * Real.sqrt (lam a j) * Real.sqrt (lam c j) : ℝ) : ℂ) =
      (p j : ℂ) * (lam a j : ℂ) * (lam c j : ℂ) := by
    rw [← Complex.ofReal_mul, show Real.sqrt (p j) * Real.sqrt (lam a j) * Real.sqrt (lam c j) *
      (Real.sqrt (p j) * Real.sqrt (lam a j) * Real.sqrt (lam c j)) =
      (Real.sqrt (p j) * Real.sqrt (p j)) * (Real.sqrt (lam a j) * Real.sqrt (lam a j)) *
      (Real.sqrt (lam c j) * Real.sqrt (lam c j)) by ring, Real.mul_self_sqrt (hp j),
      Real.mul_self_sqrt (hs.1 a j), Real.mul_self_sqrt (hs.1 c j)]
    push_cast; ring
  linear_combination ((p j : ℂ) * (star (v a j) ⬝ᵥ (S *ᵥ v c j)) *
    (star (v c j) ⬝ᵥ (S *ᵥ v a j))) * hk

lemma e38_trR {J O : Type*} [Fintype J] [DecidableEq J] [Fintype O] [DecidableEq O]
    (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hp : IsProbability p) (hs : IsSpectralData lam v) :
    Matrix.trace (∑ j, weightedState p lam v j) = 1 := by
  have h1 : ∀ i j, Matrix.trace (vecMulVec (v i j) (star (v i j))) = 1 := by
    intro i j
    rw [trace_vecMulVec, dotProduct_comm, hs.2.2 j i i, if_pos rfl]
  simp only [weightedState, rhoHat, trace_sum, trace_smul, h1, smul_eq_mul, mul_one]
  have h2 : ∀ j, ∑ i, (lam i j : ℂ) = 1 := fun j => by exact_mod_cast hs.2.1 j
  simp only [h2, mul_one]
  exact_mod_cast hp.2

theorem e38_main {J O : Type*} [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O]
    (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hp : IsProbability p) (hs : IsSpectralData lam v)
    (hfull : (rhoOut p lam v).PosDef) :
    Fcl p (comp (reversal (classicKraus lam v) (rho p)) (classicKraus lam v)) =
      ∑ j, (Matrix.trace
        (QReversal.NearOpt.invSqrt (rhoOut p lam v) * weightedState p lam v j *
         QReversal.NearOpt.invSqrt (rhoOut p lam v) * weightedState p lam v j)).re ∧
    Fcl p (comp (reversal (classicKraus lam v) (rho p)) (classicKraus lam v)) =
      1 - ∑ i, ∑ j, if i = j then 0 else
        (Matrix.trace
          (QReversal.NearOpt.invSqrt (rhoOut p lam v) * weightedState p lam v i *
           QReversal.NearOpt.invSqrt (rhoOut p lam v) * weightedState p lam v j)).re := by
  have hF : Fcl p (comp (reversal (classicKraus lam v) (rho p)) (classicKraus lam v)) =
      ∑ j, (Matrix.trace
        (QReversal.NearOpt.invSqrt (rhoOut p lam v) * weightedState p lam v j *
         QReversal.NearOpt.invSqrt (rhoOut p lam v) * weightedState p lam v j)).re :=
    Finset.sum_congr rfl fun j _ => e38_diagj p lam v hp.1 hs j
  refine ⟨hF, ?_⟩
  rw [hF]
  set S := QReversal.NearOpt.invSqrt (rhoOut p lam v) with hSdef
  set T : J → J → ℝ := fun i j =>
    (Matrix.trace (S * weightedState p lam v i * S * weightedState p lam v j)).re with hT
  have hR := e36_rhoOut p lam v hs.1
  have htot : ∑ i, ∑ j, T i j = 1 := by
    have e : ∑ i, ∑ j, Matrix.trace (S * weightedState p lam v i * S * weightedState p lam v j) =
        Matrix.trace (S * (∑ i, weightedState p lam v i) * S * (∑ j, weightedState p lam v j)) := by
      simp only [Matrix.mul_sum, Matrix.sum_mul, trace_sum]
      exact Finset.sum_comm
    have e2 : Matrix.trace (S * (∑ i, weightedState p lam v i) * S *
        (∑ j, weightedState p lam v j)) = 1 := by
      rw [← hR, hSdef, e38_SRS _ hfull, one_mul, hR, e38_trR p lam v hp hs]
    simp only [hT, ← Complex.re_sum, e, e2, Complex.one_re]
  have hrow : ∀ i, ∑ j, (if i = j then 0 else T i j) = ∑ j, T i j - T i i := by
    intro i
    have : ∑ j, (if i = j then 0 else T i j) + ∑ j, (if i = j then T i j else 0) = ∑ j, T i j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)] at this
    linarith
  change ∑ j, T j j = 1 - ∑ i, ∑ j, if i = j then 0 else T i j
  simp only [hrow, Finset.sum_sub_distrib, htot]
  ring

end QReversal.PGMBound

open QReversal.PGMBound in
theorem solution {J O : Type*} [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O]
    (p : J → ℝ) (lam : O → J → ℝ) (v : O → J → O → ℂ)
    (hp : IsProbability p) (hs : IsSpectralData lam v)
    (hfull : (rhoOut p lam v).PosDef) :
    Fcl p (comp (reversal (classicKraus lam v) (rho p)) (classicKraus lam v)) =
      ∑ j, (Matrix.trace
        (QReversal.NearOpt.invSqrt (rhoOut p lam v) * weightedState p lam v j *
         QReversal.NearOpt.invSqrt (rhoOut p lam v) * weightedState p lam v j)).re ∧
    Fcl p (comp (reversal (classicKraus lam v) (rho p)) (classicKraus lam v)) =
      1 - ∑ i, ∑ j, if i = j then 0 else
        (Matrix.trace
          (QReversal.NearOpt.invSqrt (rhoOut p lam v) * weightedState p lam v i *
           QReversal.NearOpt.invSqrt (rhoOut p lam v) * weightedState p lam v j)).re :=
  e38_main p lam v hp hs hfull
