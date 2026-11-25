-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmStar.star_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:53:14.959938+00:00
-- url     : https://prove2.me/submissions/cfbf1d26-9f10-40d4-bcbb-4396f6318e0d

import Definitions.Def_Formalism_PeriodIntegrals_QmStar
import Definitions.Def_Formalism_PeriodIntegrals_QmRowForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerProductCast_OfFnProdIntCast
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmStar_star_ofFn_prod
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmStar_ofFn_prod_intCast
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmStar_star_Tm
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmStar_prod_signs
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmStar_arg_rev

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
    (hs : ∀ a b, star (E a b) = (((ε a * ε b : ℤˣ) : ℤ) : A) * E b a) (a b : Fin t → Fin n) (w : ℂ)
    (σ : Equiv.Perm (Fin t)) :
    star ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A) *
        (List.ofFn fun k : Fin t => Tm E (w - ((k : ℕ) : ℂ)) (a (σ k)) (b k)).prod) =
      ((((∏ k, ε (a k)) * ∏ k, ε (b k) : ℤˣ) : ℤ) : A) * ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A) *
        (List.ofFn fun j : Fin t =>
          Tm E (star w - (t : ℂ) + 1 + ((j : ℕ) : ℂ)) (b j.rev) (a (σ j.rev))).prod) := by
  rw [star_mul, star_ofFn_prod]
  simp only [star_Tm E ε hs, arg_rev]
  rw [ofFn_prod_intCast (fun k : Fin t => ((ε (a (σ k.rev)) * ε (b k.rev) : ℤˣ) : ℤ))
    (fun k : Fin t => Tm E (star w - (t : ℂ) + 1 + ((k : ℕ) : ℂ)) (b k.rev) (a (σ k.rev))),
    prod_signs, star_intCast, mul_assoc, ← (Int.cast_commute _ _).eq]
end PI.UnitaryGroupMassFormula.QmStar
