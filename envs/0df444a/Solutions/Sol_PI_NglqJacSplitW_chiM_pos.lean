-- Prove2me | solution 1 for PI.NglqJacSplitW.chiM_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:57:07.298443+00:00
-- url     : https://prove2.me/submissions/15ff60dc-4d0f-45cc-9de0-1993d3725026

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_FactorOneOfDiscrete
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_GoodTransvection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal NNReal
open PI PI.NglqJacSplitW
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [LocallyCompactSpace F] [SecondCountableTopology F]
  {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PI.NglqJacSplitW
theorem _root_.solution (M : Matrix ι ι F) (hM : IsUnit M.det) : 0 < chiM M hM := by
  let _ : MeasurableSpace (ι → F) := borel _
  have _ : BorelSpace (ι → F) := ⟨rfl⟩
  exact addEquivAddHaarChar_pos (phiM M hM)
end PI.NglqJacSplitW
