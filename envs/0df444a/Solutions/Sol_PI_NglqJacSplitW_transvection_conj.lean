-- Prove2me | solution 1 for PI.NglqJacSplitW.transvection_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:57:24.036874+00:00
-- url     : https://prove2.me/submissions/15d7bde5-0753-4e77-a3ba-5147f3b32f0b

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
theorem _root_.solution {i j : ι} (hij : i ≠ j) {c : F} (hc : c ≠ 0) :
    transvection i j c = diagonal (Function.update (1 : ι → F) i c) * transvection i j 1 *
      diagonal (Function.update (1 : ι → F) i c⁻¹) := by
  ext k l
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases hk : k = i <;> by_cases hl : l = i <;> simp_all <;>
    split_ifs <;> simp_all [eq_comm]
end PI.NglqJacSplitW
