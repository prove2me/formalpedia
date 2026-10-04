-- Prove2me | solution 1 for VaryingConstants.natural_unit_values_independent_of_units
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T05:40:13.070471+00:00
-- url     : https://prove2.me/submissions/928d7d79-bc13-4cb2-86fd-167197c17513

import Mathlib
import Definitions.Def_VaryingConstants_units

open VaryingConstants in
lemma vcd10_key {a : ℝ} (ha : 0 < a) (S : ℝ) : a * Real.exp S = 1 ↔ S = -Real.log a := by
  rw [← Real.exp_log ha, ← Real.exp_add, Real.exp_eq_one_iff, Real.log_exp]
  constructor <;> intro h <;> linarith

open VaryingConstants in
lemma vcd10_prod {n d : ℕ} (D : Matrix (Fin n) (Fin d) ℝ) (s : Fin d → ℝ)
    (hs : IsPositive s) (i : Fin n) :
    ∏ k, s k ^ D i k = Real.exp (∑ k, D i k * Real.log (s k)) := by
  rw [Real.exp_sum]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [Real.rpow_def_of_pos (hs k), mul_comm]

open VaryingConstants in
theorem solution {n d : ℕ} (D : Matrix (Fin n) (Fin d) ℝ)
    (e : Fin d → Fin n) (he : (D.submatrix e id).det ≠ 0)
    (x : Fin n → ℝ) (hx : IsPositive x) (r : Fin d → ℝ) (hr : IsPositive r)
    (s s' : Fin d → ℝ) (hs : IsNaturalUnitsFor D e x s)
    (hs' : IsNaturalUnitsFor D e (unitRescale D r x) s') :
    unitRescale D s' (unitRescale D r x) = unitRescale D s x := by
  obtain ⟨hsp, hsj⟩ := hs
  obtain ⟨hsp', hsj'⟩ := hs'
  set M := D.submatrix e id with hM
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr he
  set u : Fin d → ℝ := fun k => Real.log (r k) + Real.log (s' k) - Real.log (s k) with hu_def
  have hMu : Matrix.mulVec M u = 0 := by
    funext j
    have h1 := hsj j
    have h2 := hsj' j
    change x (e j) * ∏ k, s k ^ D (e j) k = 1 at h1
    change (x (e j) * ∏ k, r k ^ D (e j) k) * ∏ k, s' k ^ D (e j) k = 1 at h2
    rw [vcd10_prod D s hsp, vcd10_key (hx _)] at h1
    rw [vcd10_prod D r hr, vcd10_prod D s' hsp', mul_assoc, ← Real.exp_add,
      vcd10_key (hx _)] at h2
    simp only [Matrix.mulVec, dotProduct, hM, hu_def, Matrix.submatrix_apply, id,
      Pi.zero_apply, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    linarith
  have hu0 : u = 0 := by
    have : u = Matrix.mulVec M⁻¹ (Matrix.mulVec M u) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
    rw [this, hMu, Matrix.mulVec_zero]
  have hk : ∀ k, Real.log (r k) + Real.log (s' k) = Real.log (s k) := by
    intro k
    have := congrFun hu0 k
    simp only [hu_def, Pi.zero_apply] at this
    linarith
  funext i
  change (x i * ∏ k, r k ^ D i k) * ∏ k, s' k ^ D i k = x i * ∏ k, s k ^ D i k
  rw [vcd10_prod D r hr, vcd10_prod D s' hsp', vcd10_prod D s hsp, mul_assoc, ← Real.exp_add,
    ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← mul_add, hk k]
