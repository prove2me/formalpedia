-- Prove2me | solution 1 for PropVolSampling.Reduction.padding
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T08:54:20.851234+00:00
-- url     : https://prove2.me/submissions/4619e968-e783-4a12-8f39-c9ecf5bccd5c

import Mathlib
import Definitions.Def_PropVolSampling_Reduction_Model

noncomputable section

open Matrix Finset

namespace PropVolSampling.Reduction.PaddingProof

lemma gram_eq_sum {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ)
    (S : Finset (Fin n)) :
    gram V S = ∑ i ∈ S, vecMulVec (fun a => V a i) (fun a => V a i) := by
  ext a b
  simp [gram, colSub, Matrix.mul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply]
  exact Finset.sum_attach S (fun i => V a i * V b i)

lemma gram_posSemidef {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ)
    (S : Finset (Fin n)) : (gram V S).PosSemidef := by
  simpa only [gram, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose (colSub V S)

lemma gram_sub_eq {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ)
    (S S' : Finset (Fin n)) (hSS' : S ⊆ S') :
    gram V S' - gram V S = gram V (S' \ S) := by
  simp only [gram_eq_sum]
  exact (Finset.sum_sdiff_eq_sub (f := fun i =>
    vecMulVec (fun a => V a i) (fun a => V a i)) hSS').symm

lemma gram_sub_posSemidef {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ)
    (S S' : Finset (Fin n)) (hSS' : S ⊆ S') :
    (gram V S' - gram V S).PosSemidef := by
  rw [gram_sub_eq V S S' hSS']
  exact gram_posSemidef V (S' \ S)

lemma gram_posDef_of_subset {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ)
    (S S' : Finset (Fin n)) (hSS' : S ⊆ S') (hpd : (gram V S).PosDef) :
    (gram V S').PosDef := by
  have h := hpd.add_posSemidef (gram_sub_posSemidef V S S' hSS')
  simpa only [add_sub_cancel] using h

/-- A completion-of-squares identity proves inverse order reversal directly over ℝ. -/
lemma inv_sub_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (hA : A.PosDef) (hB : B.PosDef)
    (hAB : (B - A).PosSemidef) : (A⁻¹ - B⁻¹).PosSemidef := by
  have hAiA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA.det_pos.ne')
  have hAAi : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA.det_pos.ne')
  have hBiB : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hB.det_pos.ne')
  have hC : (A⁻¹ - B⁻¹).IsHermitian := hA.isHermitian.inv.sub hB.isHermitian.inv
  have h₁ := hA.posSemidef.conjTranspose_mul_mul_same (A⁻¹ - B⁻¹)
  have h₂ := hAB.conjTranspose_mul_mul_same B⁻¹
  rw [hC.eq] at h₁
  rw [hB.isHermitian.inv.eq] at h₂
  have hid : (A⁻¹ - B⁻¹) * A * (A⁻¹ - B⁻¹) + B⁻¹ * (B - A) * B⁻¹ =
      A⁻¹ - B⁻¹ := by
    simp only [sub_mul, mul_sub]
    rw [hAiA, Matrix.one_mul, Matrix.one_mul, Matrix.mul_assoc B⁻¹ A A⁻¹,
      hAAi, Matrix.mul_one, hBiB, Matrix.one_mul]
    abel
  rw [← hid]
  exact h₁.add h₂

lemma trace_inv_antitone {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (hA : A.PosDef) (hB : B.PosDef)
    (hAB : (B - A).PosSemidef) : B⁻¹.trace ≤ A⁻¹.trace := by
  have h := (inv_sub_posSemidef A B hA hB hAB).trace_nonneg
  simpa only [Matrix.trace_sub, sub_nonneg] using h

lemma padding {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ)
    (S S' : Finset (Fin n)) (hSS' : S ⊆ S') (hpd : (gram V S).PosDef) :
    aObj (gram V S') ≤ aObj (gram V S) := by
  exact trace_inv_antitone (gram V S) (gram V S') hpd
    (gram_posDef_of_subset V S S' hSS' hpd) (gram_sub_posSemidef V S S' hSS')

end PropVolSampling.Reduction.PaddingProof

open PropVolSampling.Reduction

theorem solution {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ)
    (S S' : Finset (Fin n)) (hSS' : S ⊆ S') (hpd : (gram V S).PosDef) :
    aObj (gram V S') ≤ aObj (gram V S) :=
  PaddingProof.padding V S S' hSS' hpd
