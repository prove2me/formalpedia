-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.det_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:47:02.16937+00:00
-- url     : https://prove2.me/submissions/d0883004-ad22-484f-92d1-8e53b398bef3

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeH
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_DetSqSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution (M0 A : Matrix (Fin n) (Fin n) ℂ) (h : M0.det ≠ 0) :
    HasDerivAt (fun t : ℂ => (M0 + t • A).det) (M0.det * (M0⁻¹ * A).trace) 0 := by
  have hM : M0 * M0⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr h)
  set N := M0⁻¹ * A with hN
  set P : Polynomial ℂ := (det (1 + (Polynomial.X : Polynomial ℂ) • N.map Polynomial.C)).divX.divX with hP
  have e : (fun t : ℂ => (M0 + t • A).det) = fun t : ℂ => M0.det * (1 + N.trace * t + P.eval t * t ^ 2) := by
    funext t
    have : M0 + t • A = M0 * (1 + t • N) := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, hN, ← Matrix.mul_assoc, hM, Matrix.one_mul]
    rw [this, Matrix.det_mul, Matrix.det_one_add_smul]
  rw [e]
  have h1 : HasDerivAt (fun t : ℂ => 1 + N.trace * t + P.eval t * t ^ 2) N.trace 0 := by
    have ha : HasDerivAt (fun t : ℂ => N.trace * t) N.trace 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul N.trace
    have hb : HasDerivAt (fun t : ℂ => P.eval t * t ^ 2) 0 0 := by
      have := (P.hasDerivAt (0 : ℂ)).fun_mul (hasDerivAt_pow 2 (0 : ℂ))
      simpa using this
    simpa using (ha.const_add 1).fun_add hb
  exact h1.const_mul M0.det
end PositivityTheory.Rg.Sw.SP
