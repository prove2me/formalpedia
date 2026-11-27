-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesNorm_proof_1808c18190de
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:53:24.694019+00:00
-- url     : https://prove2.me/submissions/33af0337-68c6-4de7-b8fe-270f17b9051c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeriesRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeriesNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_PIntSeriesNorm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesNorm_intSeriesConv_X_3201b112e74d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesNorm_residuePart_conv_7c24ca73e8b7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesNorm_normMatrix_row_f46db8660ccd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ChowlaSelberg
open PowerSeries
open scoped Real
noncomputable section
open GroundTheory.Heights₂.Heights.ChowlaSelberg.IntSeriesNorm
namespace GroundTheory.Heights₂.Heights.ChowlaSelberg.IntSeriesNorm
theorem _root_.solution (hR : IntSeriesRing.Statement) : IntSeriesNorm.Statement := by
  intro F r hr hF p hp j
  have : NeZero p := ⟨hp.ne'⟩
  obtain ⟨⟨S, hS⟩, hmul, hhas, -, -⟩ := hR (r ^ p) (pow_nonneg hr.le p)
  by_cases hj : p < j
  · refine ⟨0, ?_, fun t _ _ ↦ ?_⟩
    · simp [IntSeriesConv]
    · rw [Multiset.esymm, Multiset.powersetCard_eq_empty _ (by simpa using hj)]
      simp [intSeriesEval]
  push Not at hj
  have hmem : ∀ i k, normMatrix F p i k ∈ S := by
    intro i k
    simp only [normMatrix, Matrix.of_apply]
    split_ifs
    · rw [one_mul, hS]; exact residuePart_conv hr hF hp _
    · exact S.mul_mem ((hS _).2 (intSeriesConv_X _)) ((hS _).2 (residuePart_conv hr hF hp _))
  let M : Matrix (Fin p) (Fin p) S := Matrix.of fun i k ↦ ⟨normMatrix F p i k, hmem i k⟩
  let e : S := (-1) ^ j * M.charpoly.coeff (p - j)
  refine ⟨e, (hS _).1 e.2, fun t ht htr ↦ ?_⟩
  have hq : ‖t ^ p‖ ≤ r ^ p := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) htr p
  let φ : S →+* ℂ := evalHom S (t ^ p)
    (fun F G ↦ hmul F G ((hS _).1 F.2) ((hS _).1 G.2) _ hq) (fun F ↦ hhas F ((hS _).1 F.2) _ hq)
  have hφ : ∀ f : S, φ f = intSeriesEval f (t ^ p) := fun _ ↦ rfl
  set ζ := Complex.exp (2 * π * Complex.I / p) with hζdef
  have hζ : IsPrimitiveRoot ζ p := Complex.isPrimitiveRoot_exp p hp.ne'
  have hexp : ∀ a : ℕ, Complex.exp (2 * π * Complex.I * a / p) = ζ ^ a := by
    intro a; rw [hζdef, ← Complex.exp_nat_mul]; congr 1; ring
  let v : Fin p → ℂ := fun a ↦ ζ ^ (a : ℕ) * t
  have hvnorm : ∀ a, ‖v a‖ ≤ r := by
    intro a; simpa [v, norm_pow, hζ.norm'_eq_one hp.ne'] using htr
  have hvpow : ∀ a, v a ^ p = t ^ p := by
    intro a
    simp only [v]
    rw [mul_pow, ← pow_mul, mul_comm (a : ℕ) p, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  have hvinj : Function.Injective v := by
    intro a b hab
    exact Fin.ext (hζ.pow_inj a.is_lt b.is_lt (mul_right_cancel₀ ht hab))
  let d : Fin p → ℂ := fun a ↦ intSeriesEval F (v a)
  let A := M.map φ
  have hA : ∀ i k, A i k = intSeriesEval (normMatrix F p i k) (t ^ p) := fun _ _ ↦ rfl
  let V := (Matrix.vandermonde v).transpose
  have hAV : A * V = V * Matrix.diagonal d := by
    ext i a
    rw [Matrix.mul_apply, Matrix.mul_diagonal]
    simp only [V, Matrix.transpose_apply, Matrix.vandermonde_apply, hA]
    rw [← hvpow a]
    exact normMatrix_row hR hr hF (v a) (hvnorm a) i
  have hdet : IsUnit V.det := by
    rw [Matrix.det_transpose, isUnit_iff_ne_zero]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hvinj
  have hchar : A.charpoly = (Matrix.diagonal d).charpoly := by
    have hconj : A = V * Matrix.diagonal d * V⁻¹ := by
      rw [← hAV, mul_assoc, Matrix.mul_nonsing_inv _ hdet, mul_one]
    rw [hconj, Matrix.charpoly_mul_comm, ← mul_assoc, Matrix.nonsing_inv_mul _ hdet, one_mul]
  have hmset : (Multiset.range p).map (fun a : ℕ ↦
      intSeriesEval F (Complex.exp (2 * π * Complex.I * a / p) * t)) =
      (Multiset.range p).map (fun a : ℕ ↦ intSeriesEval F (ζ ^ a * t)) :=
    Multiset.map_congr rfl fun a _ ↦ by rw [hexp]
  rw [hmset]
  set m := (Multiset.range p).map (fun a : ℕ ↦ intSeriesEval F (ζ ^ a * t)) with hm
  have hcard : Multiset.card m = p := by simp [hm]
  have hprod : (m.map fun x ↦ Polynomial.X - Polynomial.C x).prod = A.charpoly := by
    rw [hchar, Matrix.charpoly_diagonal]
    refine (((Fin.prod_univ_eq_prod_range
      (fun a : ℕ ↦ Polynomial.X - Polynomial.C (intSeriesEval F (ζ ^ a * t))) p)).trans ?_).symm
    rw [hm, Multiset.map_map]
    rfl
  have hcoef := Multiset.prod_X_sub_C_coeff m (k := p - j) (by omega)
  rw [hcard, Nat.sub_sub_self hj, hprod] at hcoef
  have heval : intSeriesEval (e : PowerSeries ℤ) (t ^ p) = (-1) ^ j * A.charpoly.coeff (p - j) := by
    rw [← hφ]
    show φ ((-1) ^ j * M.charpoly.coeff (p - j)) = _
    rw [map_mul, map_pow, map_neg, map_one, ← Polynomial.coeff_map, ← Matrix.charpoly_map]
  rw [heval, hcoef, ← mul_assoc, ← mul_pow]
  simp
end GroundTheory.Heights₂.Heights.ChowlaSelberg.IntSeriesNorm
