-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.det_line
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:38.039456+00:00
-- url     : https://prove2.me/submissions/c5e08a96-18af-447c-95a7-7b9a618b97b2

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.B
theorem _root_.solution (M N : Matrix (Fin n) (Fin n) ℂ) (hM : M.det ≠ 0) :
    HasDerivAt (fun t : ℝ => (M + (t : ℂ) • N).det) (M.det * (M⁻¹ * N).trace) 0 := by
  set P := M⁻¹ * N with hP
  set Q : Polynomial ℂ := Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • P.map Polynomial.C) with hQ
  have e : ∀ t : ℂ, (M + t • N).det = M.det * Q.eval t := by
    intro t
    have h1 : M + t • N = M * (1 + t • P) := by
      rw [hP, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hM), Matrix.one_mul]
    rw [h1, Matrix.det_mul, hQ, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 2
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C]
    split_ifs <;> simp
  have hp := (Polynomial.hasDerivAt Q ((0 : ℝ) : ℂ)).comp_ofReal.const_mul M.det
  have hv : Q.derivative.eval ((0 : ℝ) : ℂ) = P.trace := by
    rw [Complex.ofReal_zero, hQ]; exact Matrix.derivative_det_one_add_X_smul P
  rw [hv] at hp
  have e2 : (fun t : ℝ => (M + (t : ℂ) • N).det) = fun t : ℝ => M.det * Q.eval (t : ℂ) := funext fun t => e t
  rw [e2]; exact hp
end PositivityTheory.Rg.Sw.WR.B
