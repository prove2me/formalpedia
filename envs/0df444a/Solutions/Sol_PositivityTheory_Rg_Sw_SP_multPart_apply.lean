-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.multPart_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:57:18.449379+00:00
-- url     : https://prove2.me/submissions/c674756b-6252-4679-91ba-e00c1952bbfe

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeH
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_DetSqSplit
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeA
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_smulC

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
theorem _root_.solution (s : ℂ) (m : ℕ) (b : Bool) (k l : Fin n) (Q : Fm n) :
    multPart s m b k l Q = MvPolynomial.C (Polynomial.C (-(cB s b))) * (MvPolynomial.C (alB m b) * yv b l k * Q) := by
  rw [multPart, LinearMap.smul_apply, smulC]
  rfl
end PositivityTheory.Rg.Sw.SP
