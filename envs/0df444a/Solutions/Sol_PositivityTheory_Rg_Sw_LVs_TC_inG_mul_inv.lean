-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.inG_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:06:00.707616+00:00
-- url     : https://prove2.me/submissions/a7dd41b5-6df7-4b2a-8c96-fab41234b618

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCMatA
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BlkB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCMatB
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_inG_left_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.TC
theorem _root_.solution {g : M2 n} (hg : InG g) : g * g⁻¹ = 1 := by
  rw [Matrix.inv_eq_left_inv (inG_left_inv hg)]
  exact mul_eq_one_comm.1 (inG_left_inv hg)
end PositivityTheory.Rg.Sw.LVs.TC
