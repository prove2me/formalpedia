-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Z.clsC_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:37:34.157281+00:00
-- url     : https://prove2.me/submissions/6fb4362f-0095-4354-b3ce-86be5c9b047a

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_dP_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_dP_pos

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.Z
theorem _root_.solution (s z : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (y : E n) :
    clsC s z p q R (herm y) = cls s z p q R y := by
  unfold clsC cls uM vM evUV
  have e : (1 + Matrix.of (herm y : MC n) * Matrix.of (herm y : MC n)).det = ((dP y : ℝ) : ℂ) := dP_eq y
  rw [e, Complex.cpow_def_of_ne_zero (by exact_mod_cast (dP_pos y).ne'), mul_comm (Complex.log _) (-z)]
  rfl
end PositivityTheory.Rg.Sw.WR.Z
