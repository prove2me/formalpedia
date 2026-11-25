-- Prove2me | solution 1 for PIW.ENSpec.wreg_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:21:30.392235+00:00
-- url     : https://prove2.me/submissions/c7180bd6-fa7d-4bce-8e47-e745153d62b5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_StSpecOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_WregOfSubsingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open PIW PIW.ENSpec
open MvPolynomial RingTheory.Sequence
open scoped Pointwise
variable {S : Type u} [CommRing S]
namespace PIW.ENSpec
theorem _root_.solution {M : Type v} [AddCommGroup M] [Module S M] (rs : List S) :
    IsWeaklyRegular M (rs.map Neg.neg) ↔ IsWeaklyRegular M rs := by
  induction rs generalizing M with
  | nil => simp
  | cons r rs ih =>
    have hs : ((-r) • ⊤ : Submodule S M) = r • ⊤ := by
      rw [← Submodule.ideal_span_singleton_smul, Ideal.span_singleton_neg,
        Submodule.ideal_span_singleton_smul]
    have hreg : IsSMulRegular M (-r) ↔ IsSMulRegular M r := by
      constructor
      · intro h a b hab
        exact h (by simp only [neg_smul] at hab ⊢; exact congrArg Neg.neg hab)
      · intro h a b hab
        exact h (by simp only [neg_smul] at hab; exact neg_injective hab)
    rw [List.map_cons, isWeaklyRegular_cons_iff, isWeaklyRegular_cons_iff, hreg,
      ih (M := QuotSMulTop (-r) M)]
    exact and_congr_right fun _ =>
      (Submodule.quotEquivOfEq _ _ hs).isWeaklyRegular_congr rs
end PIW.ENSpec
