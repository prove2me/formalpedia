-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmMove.fact_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:42:34.183126+00:00
-- url     : https://prove2.me/submissions/4997dbd1-6cee-4c9c-a22a-1b8f1707e0d1

import Definitions.Def_Formalism_PeriodIntegrals_QmDefs
import Definitions.Def_Formalism_PeriodIntegrals_QmMove
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_SumPermEqSumFirstColumnSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmMove
namespace PI.UnitaryGroupMassFormula.QmMove
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] (m : ℕ) (X Y : A)
    (h : (m.factorial : A) * X = (m.factorial : A) * Y) : X = Y := by
  have hm : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  have e : ∀ Z : A, Z = algebraMap ℂ A ((m.factorial : ℂ)⁻¹) * ((m.factorial : A) * Z) := by
    intro Z
    rw [← mul_assoc, ← map_natCast (algebraMap ℂ A), ← map_mul, inv_mul_cancel₀ hm, map_one, one_mul]
  rw [e X, e Y, h]
end PI.UnitaryGroupMassFormula.QmMove
