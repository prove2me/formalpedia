-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderES.rowPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:56:59.838273+00:00
-- url     : https://prove2.me/submissions/12605095-a4d5-4e6d-81ae-60d56f4c5a00

import Definitions.Def_Formalism_PeriodIntegrals_QmBorderES
import Definitions.Def_Formalism_PeriodIntegrals_QmColExp
import Definitions.Def_Formalism_PeriodIntegrals_QmRowExp
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderSignIdentity_SkipOneEqSuccAbove
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderES_neg_one_pow_mul_self
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderES_qminor_bE_eq
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
theorem _root_.solution (hR : PI.ExpLastRow) {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (hG : GlRel E) (e : Fin n) (f : Fin t → Fin n) (b : Fin (t + 1) → Fin n) (he : ∀ x, b x ≠ e) (u : ℂ) :
    qminor E (PI.bE e f) b u = ∑ x : Fin (t + 1), (((-1 : ℤ) ^ (x : ℕ) : ℤ) : A) *
      (qminor E f (b ∘ x.succAbove) (u - 1) * E e (b x)) := by
  have h1 : (PI.bS f e ∘ Fin.castSucc) = f := by funext j; simp [PI.bS]
  have h2 : PI.bS f e (Fin.last t) = e := by simp [PI.bS]
  rw [qminor_bE_eq, hR A n t E hG (PI.bS f e) b u, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [h1, h2, Tm_of_ne E u (he x).symm, ← mul_assoc, ← Int.cast_mul, pow_add, ← mul_assoc ((-1 : ℤ) ^ t),
    neg_one_pow_mul_self, one_mul]
end PI.UnitaryGroupMassFormula.QmBorderES
