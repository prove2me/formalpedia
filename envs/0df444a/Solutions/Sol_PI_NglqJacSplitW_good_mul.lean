-- Prove2me | solution 1 for PI.NglqJacSplitW.good_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:03:19.242097+00:00
-- url     : https://prove2.me/submissions/70b36ee7-5e38-4adf-b7a6-8092685b50ec

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_FactorOneOfDiscrete
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_GoodTransvection
import Theorems.Thm_PI_NglqJacSplitW_chiM_mul
import Theorems.Thm_PI_NglqJacSplitW_modF_mul


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
theorem _root_.solution {A B : Matrix ι ι F} (hA0 : A.det ≠ 0) (hB0 : B.det ≠ 0)
    (hA : Good A) (hB : Good B) : Good (A * B) := by
  intro h
  rw [chiM_mul A B (isUnit_iff_ne_zero.mpr hA0) (isUnit_iff_ne_zero.mpr hB0) h, ENNReal.coe_mul,
    hA, hB, det_mul, modF_mul hA0 hB0]
end PI.NglqJacSplitW
