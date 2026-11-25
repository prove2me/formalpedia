-- Prove2me | solution 1 for PI.NglqJacSplitW.chiM_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:56:33.367901+00:00
-- url     : https://prove2.me/submissions/cfe98c5a-ee5f-42fd-a267-076375747e34

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
theorem _root_.solution {A B : Matrix ι ι F} (e : A = B) (hA : IsUnit A.det) (hB : IsUnit B.det) :
    chiM A hA = chiM B hB := by
  subst e
  rfl
end PI.NglqJacSplitW
