-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P24.fidelityDistance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T14:28:01.320188+00:00
-- url     : https://prove2.me/submissions/c49a7f0e-8704-4558-baac-1b6b81a05b5e

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P24

noncomputable section

open QAlgorithms MeasureTheory

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace X7M1FD

/-- Trace of an `SU(2)` matrix is real. -/
theorem X7_su2_trace_im (W : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    (W.val.trace).im = 0 := by
  have hdet : W.val.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp W.2).2
  have hU : W.val ∈ Matrix.unitaryGroup (Fin 2) ℂ := (Matrix.mem_specialUnitaryGroup_iff.mp W.2).1
  have hstar : star W.val * W.val = 1 := hU.1
  -- star W = adjugate W
  have hadj : W.val.adjugate * W.val = 1 := by
    rw [Matrix.adjugate_mul, hdet, one_smul]
  have hinv : star W.val = W.val.adjugate := by
    have h1 : star W.val * W.val * W.val.adjugate = W.val.adjugate * W.val * W.val.adjugate := by
      rw [hstar, hadj]
    have hr : W.val * W.val.adjugate = 1 := by
      rw [Matrix.mul_adjugate, hdet, one_smul]
    rwa [Matrix.mul_assoc, hr, Matrix.mul_assoc, hr, Matrix.mul_one, Matrix.mul_one] at h1
  have htr : (star W.val).trace = W.val.trace := by
    rw [hinv, Matrix.adjugate_fin_two]
    simp [Matrix.trace_fin_two]
    ring
  have : star W.val.trace = W.val.trace := by
    have e : star W.val.trace = (star W.val).trace := by
      rw [Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose]
    rw [e, htr]
  have h2 := congrArg Complex.im this
  simp at h2
  linarith

end X7M1FD

namespace QAlgorithms.Papers.Independent.Support50.P24
end QAlgorithms.Papers.Independent.Support50.P24

end

noncomputable section

open QAlgorithms MeasureTheory

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms.Papers.Independent.Support50.P24 X7M1FD in
theorem solution
    (Uin Uout : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    qubitChannelFidelity Uout.val Uin.valᴴ =
      (1 - refocusingNorm (Uout.val * Uin.val - 1)^2)^2 := by
  set W : Matrix.specialUnitaryGroup (Fin 2) ℂ := Uout * Uin with hW
  have hWv : W.val = Uout.val * Uin.val := rfl
  have him := X7_su2_trace_im W
  have hU : W.val ∈ Matrix.unitaryGroup (Fin 2) ℂ := (Matrix.mem_specialUnitaryGroup_iff.mp W.2).1
  have hstar : W.valᴴ * W.val = 1 := hU.1
  -- LHS
  have hL : qubitChannelFidelity Uout.val Uin.valᴴ = (W.val.trace.re) ^ 2 / 4 := by
    unfold qubitChannelFidelity
    have : (Uout.valᴴ * Uin.valᴴ).trace = star (W.val.trace) := by
      rw [← Matrix.conjTranspose_mul, Matrix.trace_conjTranspose, hWv, Matrix.trace_mul_comm]
    rw [this]
    simp [Complex.normSq_apply, him]
    ring
  -- RHS
  have hx : ((W.val - 1)ᴴ * (W.val - 1)).trace.re = 4 - 2 * W.val.trace.re := by
    have e : (W.val - 1)ᴴ * (W.val - 1) = W.valᴴ * W.val - W.valᴴ - W.val + 1 := by
      simp [Matrix.conjTranspose_sub, sub_mul, mul_sub]
      abel
    rw [e, hstar]
    simp [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_conjTranspose, Matrix.trace_one]
    norm_num
    ring
  have hnn : 0 ≤ ((W.val - 1)ᴴ * (W.val - 1)).trace.re := by
    have := (Matrix.posSemidef_conjTranspose_mul_self (W.val - 1)).trace_nonneg
    exact (Complex.nonneg_iff.mp this).1
  rw [hL]
  unfold refocusingNorm
  rw [← hWv, div_pow, Real.sq_sqrt hnn, hx]
  ring
