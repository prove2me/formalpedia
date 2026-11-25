-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderES.qminor_bS_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:55:08.663459+00:00
-- url     : https://prove2.me/submissions/eab87645-8ddb-412d-b884-80dad2c1ed48

import Definitions.Def_Formalism_PeriodIntegrals_QmBorderES
import Definitions.Def_Formalism_PeriodIntegrals_QmColExp
import Definitions.Def_Formalism_PeriodIntegrals_QmRowExp
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderSignIdentity_SkipOneEqSuccAbove
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderES_neg_one_pow_mul_self
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderES_qminor_bE_eq

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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmBorderES
namespace PI.UnitaryGroupMassFormula.QmBorderES
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A) (e : Fin n)
    (f : Fin t → Fin n) (b : Fin (t + 1) → Fin n) (u : ℂ) :
    qminor E (PI.bS f e) b u = (((-1 : ℤ) ^ t : ℤ) : A) * qminor E (PI.bE e f) b u := by
  rw [qminor_bE_eq E e f b u, ← mul_assoc, ← Int.cast_mul, neg_one_pow_mul_self, Int.cast_one, one_mul]
end PI.UnitaryGroupMassFormula.QmBorderES
