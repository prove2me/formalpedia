-- Prove2me | solution 1 for P2M_GapCVP_ThreeCNFReduction_sourceVariable_ne_paddingVariable__063b26f09f58
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/a0e7de59-dbba-4109-8c85-deced5a2bb12

import Mathlib
import Definitions.Def_GapCVP

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition (EvalsToInTime)
open GapCVP
open GapCVP.TraceGolf (oneStep rebound)
open GapCVP.ThreeCNFReduction
open GapCVP.CL
namespace GapCVP.ThreeCNFReduction
theorem _root_.solution {T S : ℕ}
    (v : Variable T S) :
    sourceVariable v ≠ paddingVariable₀ := by
  unfold sourceVariable paddingVariable₀
  omega
end GapCVP.ThreeCNFReduction
