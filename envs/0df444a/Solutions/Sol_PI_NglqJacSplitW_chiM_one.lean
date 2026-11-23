-- Prove2me | solution 1 for PI.NglqJacSplitW.chiM_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:35:07.274139+00:00
-- url     : https://prove2.me/submissions/4079dcf3-e683-4e31-9e10-15e346a3ce70

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
theorem _root_.solution (h : IsUnit (1 : Matrix ι ι F).det) : chiM (1 : Matrix ι ι F) h = 1 := by
  let _ : MeasurableSpace (ι → F) := borel _
  have _ : BorelSpace (ι → F) := ⟨rfl⟩
  have e : chiM (1 : Matrix ι ι F) h = addEquivAddHaarChar (phiM 1 h) := rfl
  rw [e, show phiM 1 h = ContinuousAddEquiv.refl _ from
    ContinuousAddEquiv.ext fun x => Matrix.one_mulVec x, addEquivAddHaarChar_refl]
end PI.NglqJacSplitW
