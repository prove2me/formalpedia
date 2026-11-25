-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmStar.star_qminor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:03:47.518656+00:00
-- url     : https://prove2.me/submissions/c5de5eb7-9eea-48d4-a2d5-7c28131921c7

import Definitions.Def_Formalism_PeriodIntegrals_QmStar
import Definitions.Def_Formalism_PeriodIntegrals_QmRowForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerProductCast_OfFnProdIntCast
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmStar_conjRev_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmStar_sign_conjRev
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmStar_star_term

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmStar
namespace PI.UnitaryGroupMassFormula.QmStar
theorem _root_.solution {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {n t : ℕ}
    (E : Fin n → Fin n → A) (ε : Fin n → ℤˣ)
    (hs : ∀ a b, star (E a b) = (((ε a * ε b : ℤˣ) : ℤ) : A) * E b a) (a b : Fin t → Fin n) (w : ℂ) :
    star (qminor E a b w) = ((((∏ k, ε (a k)) * ∏ k, ε (b k) : ℤˣ) : ℤ) : A) *
      PI.qminorRow E (b ∘ Fin.rev) (a ∘ Fin.rev) (star w) := by
  unfold qminor PI.qminorRow
  rw [star_sum]
  simp only [star_term E ε hs]
  rw [← Finset.mul_sum]
  congr 1
  rw [← Equiv.sum_comp (conjRev t)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [sign_conjRev]
  congr 3
  funext j
  simp [conjRev_apply, Function.comp]
end PI.UnitaryGroupMassFormula.QmStar
