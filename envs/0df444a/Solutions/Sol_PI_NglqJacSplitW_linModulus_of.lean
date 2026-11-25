-- Prove2me | solution 1 for PI.NglqJacSplitW.linModulus_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:14:57.084392+00:00
-- url     : https://prove2.me/submissions/7e1437ff-a57e-428f-866f-c7306af210a4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_FactorOneOfDiscrete
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_GoodTransvection
import Theorems.Thm_PI_NglqJacSplitW_chiM_spec
import Theorems.Thm_PI_NglqJacSplitW_good_mul
import Theorems.Thm_PI_NglqJacSplitW_good_diagonal
import Theorems.Thm_PI_NglqJacSplitW_good_transvection

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
theorem _root_.solution (hD : DiagOne) : LinModulus := by
  intro F _ _ _ _ _ _ ι _ _ _ _ M hM ν hν S _
  have hG : Good M := Matrix.diagonal_transvection_induction_of_det_ne_zero Good M hM
    (fun D hD0 => good_diagonal hD D fun i => by
      rw [det_diagonal] at hD0
      exact Finset.prod_ne_zero_iff.mp hD0 i (Finset.mem_univ i))
    (fun t => good_transvection t.i t.j t.hij t.c)
    (fun A B hA hB gA gB => good_mul hA hB gA gB)
  rw [chiM_spec M (isUnit_iff_ne_zero.mpr hM) ν S, hG]
end PI.NglqJacSplitW
