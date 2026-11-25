-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.inG_left_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:57:10.356493+00:00
-- url     : https://prove2.me/submissions/453b7130-1863-4813-9c2d-a309f9945e55

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCMatA
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BlkB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCMatB
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_jj_mul_jj

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
theorem _root_.solution {g : M2 n} (hg : InG g) : (-(JJ n) * gᴴ * JJ n) * g = 1 := by
  unfold InG at hg
  rw [show -(JJ n) * gᴴ * JJ n * g = -(JJ n) * (gᴴ * JJ n * g) by simp only [Matrix.mul_assoc], hg, neg_mul, jj_mul_jj,
    neg_neg]
end PositivityTheory.Rg.Sw.LVs.TC
