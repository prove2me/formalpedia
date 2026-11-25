-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.prime_of_not_mem_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:15:08.104233+00:00
-- url     : https://prove2.me/submissions/5e75f720-4adc-4681-ac97-113b1ec51568

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_RegDom
import Theorems.Thm_ReciprocityTheory_AnForm_R_isDomain_of_isRegularLocalRing
import Theorems.Thm_ReciprocityTheory_AnForm_R_isRegularLocalRing_quotient_of_not_mem_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open IsLocalRing
variable {R : Type*} [CommRing R]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution [IsRegularLocalRing R] {x : R}
    (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) : Prime x := by

  haveI hreg : IsRegularLocalRing (R ⧸ Ideal.span {x}) :=
    (isRegularLocalRing_quotient_of_not_mem_sq hx hx2).1
  have hdom : IsDomain (R ⧸ Ideal.span {x}) := isDomain_of_isRegularLocalRing
  have hprime : (Ideal.span {x}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp hdom
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx2 (Submodule.zero_mem _)
  exact (Ideal.span_singleton_prime hx0).mp hprime
end ReciprocityTheory.AnForm.R
