-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Z.entAn_Y
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:06.124656+00:00
-- url     : https://prove2.me/submissions/a48641da-2b26-43c8-838d-4ea9e6435003

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_an_entry

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
theorem _root_.solution (c : ℂ) (B₀ : MC n) : EntAn (fun B : MC n => 1 + c • Matrix.of B) B₀ := fun i j => by
  simp only [Matrix.add_apply, Matrix.smul_apply, of_apply, smul_eq_mul]
  exact analyticAt_const.add (analyticAt_const.mul (an_entry i j B₀))
end PositivityTheory.Rg.Sw.WR.Z
