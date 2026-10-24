-- Prove2me | solution 1 for PropVolSampling.Reduction.identity_6
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T09:02:02.661322+00:00
-- url     : https://prove2.me/submissions/60b4db19-3ca9-4b9d-ad44-6ba60b4b7ac4

import Mathlib
import Definitions.Def_PropVolSampling_Reduction_Model

noncomputable section
open Matrix Finset Polynomial
namespace PropVolSampling.Reduction.SpectralProof

lemma coeff_charpoly {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m m ℝ) (hM : M.IsHermitian) (k : ℕ) (hk : k ≤ Fintype.card m) :
    M.charpoly.coeff (Fintype.card m-k) = (-1:ℝ)^k * Ek k M := by
  have h := Polynomial.coeff_eq_esymm_roots_of_splits hM.splits_charpoly
    (show Fintype.card m-k ≤ M.charpoly.natDegree by
      rw [Matrix.charpoly_natDegree_eq_dim]; omega)
  simpa only [Matrix.charpoly_natDegree_eq_dim, (Matrix.charpoly_monic M).leadingCoeff,
    one_mul, Nat.sub_sub_self hk, Ek] using h

end PropVolSampling.Reduction.SpectralProof

open PropVolSampling.Reduction PropVolSampling.Reduction.SpectralProof

theorem solution {d : ℕ} (hd : 1 ≤ d) (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : M.IsHermitian) (hdet : M.det ≠ 0) :
    aObj M = Ek (d-1) M / M.det := by
  let : NeZero d := ⟨by omega⟩
  have hu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hc := Matrix.charpoly_inv M hu
  have hp : M⁻¹.charpoly = Polynomial.C (((-1:ℝ)^d)*M.det⁻¹) * M.charpoly.reverse := by
    simpa only [Fintype.card_fin, Ring.inverse_eq_inv,
      show (-1 : ℝ[X])^d = Polynomial.C ((-1:ℝ)^d) by simp,
      ← Polynomial.C_mul, ← Matrix.reverse_charpoly] using hc
  have htrace : aObj M = - (((-1:ℝ)^d)*M.det⁻¹ * M.charpoly.coeff 1) := by
    unfold aObj
    rw [Matrix.trace_eq_neg_charpoly_coeff, hp, Polynomial.coeff_C_mul,
      Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim]
    simp only [Fintype.card_fin, Polynomial.revAt_le (by omega : d-1 ≤ d),
      Nat.sub_sub_self hd]
  have hv := coeff_charpoly M hM (d-1) (by simp)
  simp only [Fintype.card_fin, Nat.sub_sub_self hd] at hv
  rw [htrace, hv]
  have hs : (-1:ℝ)^d = -((-1:ℝ)^(d-1)) := by
    conv_lhs => rw [show d=(d-1)+1 by omega, pow_succ]
    ring
  have hsq : ((-1:ℝ)^(d-1))*((-1:ℝ)^(d-1)) = 1 := by
    rw [←mul_pow]
    simp
  rw [hs, div_eq_mul_inv]
  calc
    _ = (((-1:ℝ)^(d-1))*((-1:ℝ)^(d-1))) * Ek (d-1) M * M.det⁻¹ := by ring
    _ = _ := by rw [hsq, one_mul]
