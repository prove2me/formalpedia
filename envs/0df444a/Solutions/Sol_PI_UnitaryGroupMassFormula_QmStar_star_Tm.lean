-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmStar.star_Tm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:42:53.47633+00:00
-- url     : https://prove2.me/submissions/40fa7f0e-68f8-47b2-85ae-c85d44a314aa

import Definitions.Def_Formalism_PeriodIntegrals_QmStar
import Definitions.Def_Formalism_PeriodIntegrals_QmRowForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerProductCast_OfFnProdIntCast

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
theorem _root_.solution {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {n : ℕ}
    (E : Fin n → Fin n → A) (ε : Fin n → ℤˣ)
    (hs : ∀ a b, star (E a b) = (((ε a * ε b : ℤˣ) : ℤ) : A) * E b a) (u : ℂ) (c d : Fin n) :
    star (Tm E u c d) = (((ε c * ε d : ℤˣ) : ℤ) : A) * Tm E (star u) d c := by
  unfold Tm
  rw [star_add, hs]
  by_cases h : c = d
  · subst h
    rw [if_pos rfl, if_pos rfl, Int.units_mul_self, Units.val_one, Int.cast_one, one_mul,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, star_smul, star_one]
    exact (one_mul _).symm
  · rw [if_neg h, if_neg (Ne.symm h), star_zero, zero_add, zero_add]
end PI.UnitaryGroupMassFormula.QmStar
