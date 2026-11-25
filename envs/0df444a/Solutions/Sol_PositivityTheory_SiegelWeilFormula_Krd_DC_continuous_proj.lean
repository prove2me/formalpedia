-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.Krd.DC.continuous_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:57:41.897472+00:00
-- url     : https://prove2.me/submissions/1468df7a-3581-4d51-992e-0eeac0a3fb8c

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
theorem _root_.solution (J : Matrix ι ι ℂ) (d : ℂ) : Continuous (proj J d) := by
  unfold proj
  have h1 : Continuous fun Y : Matrix ι ι ℂ => J * Yᴴ * J :=
    (continuous_const.mul continuous_id.matrix_conjTranspose).mul continuous_const
  exact continuous_id.sub (h1.const_smul d⁻¹)
end PositivityTheory.SiegelWeilFormula.Krd.DC
