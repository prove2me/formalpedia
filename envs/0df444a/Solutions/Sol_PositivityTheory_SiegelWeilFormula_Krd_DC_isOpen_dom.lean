-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.Krd.DC.isOpen_dom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:57:15.395001+00:00
-- url     : https://prove2.me/submissions/679f4bab-0f2a-4ea0-9a47-68477a35c423

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
theorem _root_.solution : IsOpen {Y : Matrix ι ι ℂ | IsUnit (1 - Y).det} := by
  have hc : Continuous fun Y : Matrix ι ι ℂ => (1 - Y).det :=
    (continuous_const.sub continuous_id).matrix_det
  have he : {Y : Matrix ι ι ℂ | IsUnit (1 - Y).det} = (fun Y : Matrix ι ι ℂ => (1 - Y).det) ⁻¹' {0}ᶜ := by
    ext Y
    simp [isUnit_iff_ne_zero]
  rw [he]
  exact isOpen_compl_singleton.preimage hc
end PositivityTheory.SiegelWeilFormula.Krd.DC
