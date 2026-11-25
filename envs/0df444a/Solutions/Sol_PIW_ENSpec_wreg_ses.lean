-- Prove2me | solution 1 for PIW.ENSpec.wreg_ses
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:23:42.485207+00:00
-- url     : https://prove2.me/submissions/6af7b3b3-7ec4-47d2-bc7e-0d9905dceabe

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
theorem _root_.solution (rs : List S) : ∀ {M' M M'' : Type v} [AddCommGroup M'] [Module S M'] [AddCommGroup M]
    [Module S M] [AddCommGroup M''] [Module S M''] (f : M' →ₗ[S] M) (g : M →ₗ[S] M''),
    Function.Injective f → Function.Exact f g → Function.Surjective g →
    IsWeaklyRegular M' rs → IsWeaklyRegular M'' rs → IsWeaklyRegular M rs := by
  induction rs with
  | nil => intros; exact IsWeaklyRegular.nil S _
  | cons r rs ih =>
    intro M' M M'' _ _ _ _ _ _ f g hf hfg hg h1 h2
    rw [isWeaklyRegular_cons_iff] at h1 h2 ⊢
    refine ⟨isSMulRegular_of_range_eq_ker hf hfg.linearMap_ker_eq.symm h1.1 h2.1, ?_⟩
    refine ih (QuotSMulTop.map r f) (QuotSMulTop.map r g) ?_ (QuotSMulTop.map_exact r hfg hg)
      (QuotSMulTop.map_surjective r hg) h1.2 h2.2
    have h0 : Function.Exact (0 : PUnit.{v + 1} →ₗ[S] M') f :=
      (LinearMap.exact_zero_iff_injective _ f).2 hf
    have he := QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last h0 hfg h2.1
    rw [map_zero] at he
    exact (LinearMap.exact_zero_iff_injective _ _).1 he
end PIW.ENSpec
