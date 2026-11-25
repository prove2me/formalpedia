-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderES.colPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:03:49.76009+00:00
-- url     : https://prove2.me/submissions/1f2e3a52-4e08-40c2-93ea-68b9320922b7

import Definitions.Def_Formalism_PeriodIntegrals_QmBorderES
import Definitions.Def_Formalism_PeriodIntegrals_QmColExp
import Definitions.Def_Formalism_PeriodIntegrals_QmRowExp
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderSignIdentity_SkipOneEqSuccAbove
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderES_qminor_bS_eq
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderES_Tm_of_ne

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
theorem _root_.solution (hF : PI.ExpFirstRow) {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (hG : GlRel E) (e : Fin n) (f : Fin t → Fin n) (b : Fin (t + 1) → Fin n) (he : ∀ x, b x ≠ e) (u : ℂ) :
    qminor E (PI.bS f e) b u = ∑ x : Fin (t + 1), (((-1 : ℤ) ^ (t + (x : ℕ)) : ℤ) : A) *
      (E e (b x) * qminor E f (b ∘ x.succAbove) u) := by
  have h1 : (PI.bE e f ∘ Fin.succ) = f := by funext j; simp [PI.bE]
  have h2 : PI.bE e f 0 = e := by simp [PI.bE]
  rw [qminor_bS_eq, hF A n t E hG (PI.bE e f) b u, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [h1, h2, Tm_of_ne E (u - (t : ℂ)) (he x).symm, ← mul_assoc, ← Int.cast_mul, pow_add]
end PI.UnitaryGroupMassFormula.QmBorderES
