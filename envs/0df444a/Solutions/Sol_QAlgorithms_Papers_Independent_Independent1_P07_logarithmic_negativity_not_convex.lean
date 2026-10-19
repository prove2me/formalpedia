-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P07.logarithmic_negativity_not_convex
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:06:24.409509+00:00
-- url     : https://prove2.me/submissions/8cd63494-4926-48af-859f-7e64beec32e0

import Mathlib
import Definitions.Def_QAlgorithms_Defs_EntanglementNegativity
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P07_Model
set_option autoImplicit false

/-! Vidal–Werner, arXiv:quant-ph/0102117v1. All locators are PDF pages.
Paper-local operational and variational definitions precede their statements.
Deferred source inconsistencies and interfaces are recorded in HARD.md. -/

noncomputable section

open scoped Matrix ComplexOrder NNReal ENNReal

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Independent1 QAlgorithms.Papers.Independent.Independent1.P07
open Entanglement

/-- §II.A, PDF p. 3: only nonconvexity, without the erroneous LOCC-increase inference. -/
theorem gq_dummy_nc : True := trivial

open scoped MatrixOrder in
theorem gq_tn {ι : Type*} [Fintype ι] [DecidableEq ι] (M S : Matrix ι ι ℂ) (hS : S.PosSemidef)
    (h : Mᴴ * M = S * S) : traceNorm M = S.trace.re := by
  unfold traceNorm
  rw [h]
  have h0 : (0 : Matrix ι ι ℂ) ≤ S := hS.nonneg
  have h1 : (0 : Matrix ι ι ℂ) ≤ S * S := by
    have := Matrix.posSemidef_conjTranspose_mul_self S
    rw [hS.isHermitian.eq] at this
    exact this.nonneg
  rw [← cfcₙ_eq_cfc, ← CFC.sqrt_eq_real_sqrt _ h1, CFC.sqrt_mul_self S h0]

def gq_v : (Bool × Bool) → ℂ := fun p => if p.1 = p.2 then 1 else 0
def gq_e : (Bool × Bool) → ℂ := fun p => if p = (false, false) then 1 else 0
def gq_rho : Matrix (Bool × Bool) (Bool × Bool) ℂ := (1/2 : ℂ) • Matrix.vecMulVec gq_v (star gq_v)
def gq_sig : Matrix (Bool × Bool) (Bool × Bool) ℂ := Matrix.vecMulVec gq_e (star gq_e)

theorem gq_ln_rho : logNeg gq_rho = 1 := by
  unfold logNeg
  rw [gq_tn _ ((1/2 : ℂ) • (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ))]
  · simp [Matrix.trace, Fintype.sum_prod_type]; norm_num
  · exact Matrix.PosSemidef.one.smul (by norm_num [Complex.le_def])
  · ext ⟨a, b⟩ ⟨c, d⟩
    cases a <;> cases b <;> cases c <;> cases d <;>
      simp [Matrix.mul_apply, Fintype.sum_prod_type, partialTransposeFirst, gq_rho, gq_v,
        Matrix.vecMulVec_apply, Matrix.one_apply, map_ofNat] <;> norm_num

theorem gq_ln_sig : logNeg gq_sig = 0 := by
  unfold logNeg
  rw [gq_tn _ gq_sig]
  · simp [Matrix.trace, Fintype.sum_prod_type, gq_sig, gq_e, Matrix.vecMulVec_apply]
  · exact Matrix.posSemidef_vecMulVec_self_star _
  · ext ⟨a, b⟩ ⟨c, d⟩
    cases a <;> cases b <;> cases c <;> cases d <;>
      simp [Matrix.mul_apply, Fintype.sum_prod_type, partialTransposeFirst, gq_sig, gq_e,
        Matrix.vecMulVec_apply]

theorem gq_ln_mix : logNeg ((1/2 : ℂ) • gq_rho + (1/2 : ℂ) • gq_sig) = Real.logb 2 (3/2) := by
  unfold logNeg
  rw [gq_tn _ ((1/4 : ℂ) • (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) + (1/2 : ℂ) • gq_sig)]
  · simp [Matrix.trace, Fintype.sum_prod_type, gq_sig, gq_e, Matrix.vecMulVec_apply]; norm_num
  · exact (Matrix.PosSemidef.one.smul (by norm_num [Complex.le_def])).add
      ((Matrix.posSemidef_vecMulVec_self_star _).smul (by norm_num [Complex.le_def]))
  · ext ⟨a, b⟩ ⟨c, d⟩
    cases a <;> cases b <;> cases c <;> cases d <;>
      simp [Matrix.mul_apply, Fintype.sum_prod_type, partialTransposeFirst, gq_rho, gq_v, gq_sig, gq_e,
        Matrix.vecMulVec_apply, Matrix.one_apply, map_ofNat] <;> norm_num

theorem solution :
    ∃ rho sigma : Matrix (Bool × Bool) (Bool × Bool) ℂ,
      IsDensityMatrix rho ∧ IsDensityMatrix sigma ∧
      (logNeg rho+logNeg sigma)/2 < logNeg ((1/2 : ℂ) • rho+(1/2 : ℂ) • sigma) := by
  refine ⟨gq_rho, gq_sig, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by norm_num [Complex.le_def])
  · simp [Matrix.trace, Fintype.sum_prod_type, gq_rho, gq_v, Matrix.vecMulVec_apply]
  · exact Matrix.posSemidef_vecMulVec_self_star _
  · simp [Matrix.trace, Fintype.sum_prod_type, gq_sig, gq_e, Matrix.vecMulVec_apply]
  · rw [gq_ln_rho, gq_ln_sig, gq_ln_mix]
    rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num),
      show ((1:ℝ)+0)/2 = 1/2 by norm_num, ← Real.sqrt_eq_rpow]
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num

