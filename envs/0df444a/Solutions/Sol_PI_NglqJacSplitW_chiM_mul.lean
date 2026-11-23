-- Prove2me | solution 1 for PI.NglqJacSplitW.chiM_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:35:07.480031+00:00
-- url     : https://prove2.me/submissions/2bb1b982-033d-4844-a83c-aa67783dfba5

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
theorem _root_.solution (A B : Matrix ι ι F) (hA : IsUnit A.det) (hB : IsUnit B.det)
    (hAB : IsUnit (A * B).det) : chiM (A * B) hAB = chiM A hA * chiM B hB := by
  let _ : MeasurableSpace (ι → F) := borel _
  have _ : BorelSpace (ι → F) := ⟨rfl⟩
  have e : ∀ (N : Matrix ι ι F) (hN : IsUnit N.det), chiM N hN = addEquivAddHaarChar (phiM N hN) :=
    fun _ _ => rfl
  rw [e, e, e, show phiM (A * B) hAB = (phiM B hB).trans (phiM A hA) from
    ContinuousAddEquiv.ext fun x => (Matrix.mulVec_mulVec x A B).symm, addEquivAddHaarChar_trans, mul_comm]
end PI.NglqJacSplitW
