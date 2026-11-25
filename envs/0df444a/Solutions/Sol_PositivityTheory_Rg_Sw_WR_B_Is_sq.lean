-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.Is_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:59:16.515848+00:00
-- url     : https://prove2.me/submissions/b66374b8-6365-4d2d-aed1-ed7a9e0be19a

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_sq_of_pm

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
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.B
theorem _root_.solution {s : ℂ} (hs : s = 1 ∨ s = -1) : (Complex.I * s) * (Complex.I * s) = -1 := by
  rw [mul_mul_mul_comm, Complex.I_mul_I, sq_of_pm hs]
  ring
end PositivityTheory.Rg.Sw.WR.B
