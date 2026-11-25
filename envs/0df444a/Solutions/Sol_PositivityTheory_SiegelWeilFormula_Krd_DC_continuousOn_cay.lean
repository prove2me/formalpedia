-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.Krd.DC.continuousOn_cay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:06:14.017343+00:00
-- url     : https://prove2.me/submissions/8ca7ab52-c471-4748-8ac2-50938dd9d554

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_CayleyTransform_DenseCP
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_CayleyTransform_DenseC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.Krd PositivityTheory.SiegelWeilFormula.Krd.DC
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PositivityTheory.SiegelWeilFormula.Krd.DC
theorem _root_.solution : ContinuousOn (cay (ι := ι)) {Y | IsUnit (1 - Y).det} := by
  intro Y hY
  apply ContinuousAt.continuousWithinAt
  have hinv : ContinuousAt (fun Z : Matrix ι ι ℂ => (1 - Z)⁻¹) Y := by
    have h1 : ContinuousAt Inv.inv (1 - Y) := by
      apply continuousAt_matrix_inv
      have h2 := NormedRing.inverse_continuousAt hY.unit
      rwa [hY.unit_spec] at h2
    exact h1.comp (continuous_const.sub continuous_id).continuousAt
  show ContinuousAt (fun Z : Matrix ι ι ℂ => (1 + Z) * (1 - Z)⁻¹) Y
  exact (continuous_const.add continuous_id).continuousAt.mul hinv
end PositivityTheory.SiegelWeilFormula.Krd.DC
