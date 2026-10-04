-- Prove2me | solution 1 for VaryingConstants.natural_units_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T05:23:30.247001+00:00
-- url     : https://prove2.me/submissions/80fadbd7-f2f0-4dc3-a09b-7d9a5bd2ff93

import Mathlib
import Definitions.Def_VaryingConstants_units

open VaryingConstants in
lemma vc432_key {a : ℝ} (ha : 0 < a) (S : ℝ) : a * Real.exp S = 1 ↔ S = -Real.log a := by
  rw [← Real.exp_log ha, ← Real.exp_add, Real.exp_eq_one_iff, Real.log_exp]
  constructor <;> intro h <;> linarith

open VaryingConstants in
lemma vc432_prod {n d : ℕ} (D : Matrix (Fin n) (Fin d) ℝ) (s : Fin d → ℝ)
    (hs : IsPositive s) (i : Fin n) :
    ∏ k, s k ^ D i k = Real.exp (∑ k, D i k * Real.log (s k)) := by
  rw [Real.exp_sum]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [Real.rpow_def_of_pos (hs k), mul_comm]

open VaryingConstants in
theorem solution {n d : ℕ} (D : Matrix (Fin n) (Fin d) ℝ)
    (e : Fin d → Fin n) (he : (D.submatrix e id).det ≠ 0)
    (x : Fin n → ℝ) (hx : IsPositive x) :
    ∃! s : Fin d → ℝ, IsNaturalUnitsFor D e x s := by
  set M := D.submatrix e id with hM
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr he
  set b : Fin d → ℝ := fun j => -Real.log (x (e j)) with hb
  set t : Fin d → ℝ := Matrix.mulVec M⁻¹ b with ht
  have hMt : Matrix.mulVec M t = b := by
    rw [ht, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have hpos : IsPositive (fun k => Real.exp (t k)) := fun k => Real.exp_pos _
  refine ⟨fun k => Real.exp (t k), ⟨hpos, fun j => ?_⟩, ?_⟩
  · show x (e j) * ∏ k, Real.exp (t k) ^ D (e j) k = 1
    rw [vc432_prod D _ hpos, vc432_key (hx _)]
    have := congrFun hMt j
    simp only [Real.log_exp]
    simpa [Matrix.mulVec, dotProduct, hM, hb] using this
  · rintro s ⟨hs, hj⟩
    have h1 : Matrix.mulVec M (fun k => Real.log (s k)) = b := by
      funext j
      have := hj j
      change x (e j) * ∏ k, s k ^ D (e j) k = 1 at this
      rw [vc432_prod D s hs, vc432_key (hx _)] at this
      simpa [Matrix.mulVec, dotProduct, hM, hb] using this
    have h2 : (fun k => Real.log (s k)) = t := by
      rw [ht, ← h1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
    funext k
    rw [← congrFun h2 k]
    exact (Real.exp_log (hs k)).symm
