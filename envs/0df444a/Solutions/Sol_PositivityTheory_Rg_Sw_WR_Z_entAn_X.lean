-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Z.entAn_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:05.922397+00:00
-- url     : https://prove2.me/submissions/39a4f22f-b4a8-4b19-95cb-9876a62f21c9

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
theorem _root_.solution (c : ℂ) (B₀ : MC n) : EntAn (fun B : MC n => 1 - c • Matrix.of B) B₀ := fun i j => by
  simp only [Matrix.sub_apply, Matrix.smul_apply, of_apply, smul_eq_mul]
  exact analyticAt_const.sub (analyticAt_const.mul (an_entry i j B₀))
end PositivityTheory.Rg.Sw.WR.Z
