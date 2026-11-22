-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderFull.tm_comm_E
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:18:04.997791+00:00
-- url     : https://prove2.me/submissions/ea0e36cf-1f2f-47db-a212-f4f740d37ad5

import Definitions.Def_Formalism_PeriodIntegrals_QmBorderFull
import Definitions.Def_Formalism_PeriodIntegrals_QmBorderES
import Definitions.Def_Formalism_PeriodIntegrals_QmColExp
import Definitions.Def_Formalism_PeriodIntegrals_QmRowExp
import Definitions.Def_Formalism_PeriodIntegrals_QmSkip
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_Development

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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmBorderFull
open PI
namespace PI.UnitaryGroupMassFormula.QmBorderFull
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E)
    (u : ℂ) (e c d : Fin n) (h1 : e ≠ c) (h2 : d ≠ e) : Tm E u e e * E c d = E c d * Tm E u e e := by
  have h := hE e e c d
  rw [if_neg h1, if_neg h2, sub_zero, sub_eq_zero] at h
  rw [Formalism.REAL.Tm, if_pos rfl, add_mul, mul_add, Algebra.commutes, h]
end PI.UnitaryGroupMassFormula.QmBorderFull
