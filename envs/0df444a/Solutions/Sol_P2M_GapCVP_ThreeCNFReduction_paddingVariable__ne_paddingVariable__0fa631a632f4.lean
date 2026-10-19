-- Prove2me | solution 1 for P2M_GapCVP_ThreeCNFReduction_paddingVariable__ne_paddingVariable__0fa631a632f4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/f1f71e69-7fd7-4ccc-9827-d729f63c1081

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
theorem _root_.solution :
    paddingVariable₀ ≠ paddingVariable₁ := by
  decide
end GapCVP.ThreeCNFReduction
