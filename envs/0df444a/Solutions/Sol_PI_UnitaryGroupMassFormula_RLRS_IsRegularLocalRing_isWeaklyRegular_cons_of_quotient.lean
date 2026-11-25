-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing.isWeaklyRegular_cons_of_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:42:20.129831+00:00
-- url     : https://prove2.me/submissions/3f8cd518-7c22-4234-a077-05749025a294

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RegularLocalRegularSequence_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RegularLocalRegularSequence_ExistsIsRegularOfListEqMaximalIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.RLRS
open PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing
open IsLocalRing RingTheory.Sequence
open scoped Pointwise
universe u
namespace PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing
theorem _root_.solution {A : Type u} [CommRing A] {x : A}
    (hx : IsSMulRegular A x) (ys : List A)
    (hys : IsWeaklyRegular (A ⧸ Ideal.span ({x} : Set A))
      (ys.map (Ideal.Quotient.mk (Ideal.span ({x} : Set A))))) :
    IsWeaklyRegular A (x :: ys) := by
  rw [isWeaklyRegular_cons_iff]
  refine ⟨hx, ?_⟩
  have h : (x • ⊤ : Submodule A A) = Ideal.span ({x} : Set A) := by
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
  have e : QuotSMulTop x A ≃ₗ[A] A ⧸ Ideal.span ({x} : Set A) :=
    Submodule.quotEquivOfEq _ _ h
  rw [e.isWeaklyRegular_congr]
  refine (isWeaklyRegular_map_algebraMap_iff (A ⧸ Ideal.span ({x} : Set A))
    (A ⧸ Ideal.span ({x} : Set A)) ys).mp ?_
  rw [Ideal.Quotient.algebraMap_eq]
  exact hys
end PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing
