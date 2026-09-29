-- Prove2me | solution 1 for RobustLS.Tikhonov.tikhonov_formula
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:22:01.10995+00:00
-- url     : https://prove2.me/submissions/b69e6100-ffc8-4d18-aba3-378f75f58c6b

import Mathlib
import Definitions.Def_RobustLS_Tikhonov_Core

namespace RobustLS.Tikhonov

open Matrix

lemma aux_tik_sq {ι : Type*} [Fintype ι] (v : ι → ℝ) : eucNorm v ^ 2 = ∑ i, v i ^ 2 := by
  unfold eucNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (v i)))]

lemma aux_tik_stack {m : ℕ} (x : Fin m → ℝ) :
    eucNorm (stackOne x) = Real.sqrt (eucNorm x ^ 2 + 1) := by
  rw [aux_tik_sq]
  unfold eucNorm stackOne
  rw [Fintype.sum_sum_type]
  simp

end RobustLS.Tikhonov

open RobustLS.Tikhonov
open Matrix

theorem solution {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ)
    (x : Fin m → ℝ) (lam tau : ℝ) (z : Fin n → ℝ) (u : Fin m → ℝ)
    (hopt : IsSOCPOptimal A b x lam tau) (hlt : tau < lam)
    (hlin : Aᵀ *ᵥ z + u = 0)
    (hz : z = (-(1 / eucNorm (A *ᵥ x - b))) • (A *ᵥ x - b))
    (hu : u = (-(1 / Real.sqrt (eucNorm x ^ 2 + 1))) • x) :
    (lam - tau) / tau = eucNorm (A *ᵥ x - b) / Real.sqrt (eucNorm x ^ 2 + 1) ∧
      x = (Aᵀ * A + ((lam - tau) / tau) • (1 : Matrix (Fin m) (Fin m) ℝ))⁻¹ *ᵥ (Aᵀ *ᵥ b) := by
  obtain ⟨⟨h1, h2⟩, hmin⟩ := hopt
  rw [aux_tik_stack] at h2
  set r := eucNorm (A *ᵥ x - b) with hr
  set s := Real.sqrt (eucNorm x ^ 2 + 1) with hs
  have hs1 : 1 ≤ s := by
    have := Real.sqrt_le_sqrt (show (1:ℝ) ≤ eucNorm x ^ 2 + 1 by nlinarith [sq_nonneg (eucNorm x)])
    simpa [hs] using this
  have hfeas : IsSOCPFeasible A b x (r + s) s := by
    refine ⟨by rw [add_sub_cancel_right], ?_⟩
    rw [aux_tik_stack]
  have hle := hmin x (r + s) s hfeas
  have htau : tau = s := by linarith
  have hlt2 : lam - tau = r := by linarith
  have hr0 : 0 < r := by linarith
  have hs0 : 0 < s := by linarith
  have hmu : (lam - tau) / tau = r / s := by rw [hlt2, htau]
  refine ⟨hmu, ?_⟩
  rw [hmu]
  have hlin' : Aᵀ *ᵥ (A *ᵥ x - b) + (r / s) • x = 0 := by
    rw [hz, hu, Matrix.mulVec_smul] at hlin
    have := congrArg (fun v => (-r) • v) hlin
    simp only [smul_add, smul_smul, smul_zero] at this
    convert this using 2
    · rw [show -r * -(1 / r) = 1 by field_simp, one_smul]
    · congr 1
      field_simp
  set M := Aᵀ * A + (r / s) • (1 : Matrix (Fin m) (Fin m) ℝ) with hM
  have hMx : M *ᵥ x = Aᵀ *ᵥ b := by
    rw [hM, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [Matrix.mulVec_sub] at hlin'
    rw [← sub_eq_zero, ← hlin']
    abel
  have hpd : M.PosDef := by
    rw [hM]
    refine Matrix.PosDef.posSemidef_add ?_ ?_
    · simpa using Matrix.posSemidef_conjTranspose_mul_self A
    · exact Matrix.PosDef.one.smul (div_pos hr0 hs0)
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hpd.isUnit
  rw [← hMx, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
