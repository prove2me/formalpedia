-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.cls_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:36:57.493447+00:00
-- url     : https://prove2.me/submissions/6713838d-9c86-4702-b040-6158cc197191

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Lagr
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBFinal
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_det_u_mul_det_v

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.K.GB
theorem _root_.solution (s : ℂ) (hs : s = 1 ∨ s = -1) (i p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) :
    cls s (i : ℂ) p q R = cls s 0 (p + i) (q + i) R := by
  funext y
  have h := det_u_mul_det_v s hs y
  simp only [cls, neg_zero, Complex.cpow_zero, one_mul, Complex.cpow_neg, Complex.cpow_natCast, pow_add]
  rw [show ((((dP y : ℝ) : ℂ)) ^ i)⁻¹ = ((uM s y).det * (vM s y).det) ^ i by rw [h, inv_pow]]
  ring
end PositivityTheory.Rg.Sw.WR.K.GB
