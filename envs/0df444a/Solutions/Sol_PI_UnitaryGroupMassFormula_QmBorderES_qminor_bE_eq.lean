-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderES.qminor_bE_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:47:09.852237+00:00
-- url     : https://prove2.me/submissions/dd7f53cd-d12e-4a38-9061-12daa05b60f9

import Definitions.Def_Formalism_PeriodIntegrals_QmBorderES
import Definitions.Def_Formalism_PeriodIntegrals_QmColExp
import Definitions.Def_Formalism_PeriodIntegrals_QmRowExp
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderSignIdentity_SkipOneEqSuccAbove
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderES_cons_comp_finRotate

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
    qminor E (PI.bE e f) b u = (((-1 : ℤ) ^ t : ℤ) : A) * qminor E (PI.bS f e) b u := by
  have key : ∀ (a a' : Fin (t + 1) → Fin n) (ρ : Equiv.Perm (Fin (t + 1))), a ∘ ρ = a' →
      qminor E a b u = ((Equiv.Perm.sign ρ : ℤ) : A) * qminor E a' b u := by
    intro a a' ρ hρ
    unfold qminor
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft ρ⁻¹) _ _ (fun σ => ?_)
    have hu : Equiv.Perm.sign σ = Equiv.Perm.sign ρ * Equiv.Perm.sign (ρ⁻¹ * σ) := by
      rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, ← mul_assoc, Int.units_mul_self, one_mul]
    have hp : (List.ofFn fun k : Fin (t + 1) => Tm E (u - (k : ℂ)) (a (σ k)) (b k)) =
        List.ofFn fun k : Fin (t + 1) => Tm E (u - (k : ℂ)) (a' ((ρ⁻¹ * σ) k)) (b k) := by
      congr 1
      funext k
      rw [← hρ]
      simp [Equiv.Perm.mul_apply]
    rw [Equiv.coe_mulLeft, hu, Units.val_mul, Int.cast_mul, hp, mul_assoc]
  rw [key (PI.bE e f) (PI.bS f e) (finRotate (t + 1)) (cons_comp_finRotate e f), sign_finRotate]
  push_cast
  rfl
end PI.UnitaryGroupMassFormula.QmBorderES
