-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.WMult.ord_isLocalization_eq_exponent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:01:05.782899+00:00
-- url     : https://prove2.me/submissions/f3c2492b-61f9-413a-ae92-0a1a2007e86f

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsBasicOpenCover
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WMultA
import Theorems.Thm_ReciprocityTheory_AnForm_R_ord_localization_eq_exponent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.AnForm.R.WMult
open AlgebraicGeometry CategoryTheory IsLocalRing
variable {W : Scheme.{0}}
private theorem ring_ord_ringEquiv_apply {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (z : A) : Ring.ord B (e z) = Ring.ord A z := by
  have hI : Ideal.comap e (Ideal.span {e z}) = Ideal.span {z} := by
    rw [show Ideal.span {e z} = Ideal.map e (Ideal.span {z}) by rw [Ideal.map_span, Set.image_singleton]]
    exact Ideal.comap_map_of_bijective e e.bijective
  unfold Ring.ord
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  refine Order.krullDim_eq_of_orderIso ?_
  let o3 := Ideal.relIsoOfBijective (e : A →+* B) e.bijective
  have h3 : o3 (Ideal.span {e z}) = Ideal.span {z} := hI
  exact (Submodule.comapMkQRelIso _).trans (((o3.Ici _).trans
    (OrderIso.setCongr _ _ (by rw [h3]))).trans (Submodule.comapMkQRelIso _).symm)
end ReciprocityTheory.AnForm.R.WMult
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.WMult
open AlgebraicGeometry CategoryTheory IsLocalRing
variable {W : Scheme.{0}}
namespace ReciprocityTheory.AnForm.R.WMult
theorem _root_.solution {R : Type*} [CommRing R] [IsRegularLocalRing R] {n : ℕ}
    (f : Fin n → R)
    (hspan : Ideal.span (Set.range f) = maximalIdeal R) (hdim : (n : WithBot ℕ∞) = ringKrullDim R)
    (J : Finset (Fin n)) (u : Rˣ) (m : Fin n → ℕ) (i : Fin n) (hi : i ∈ J)
    [(Ideal.span {f i}).IsPrime] (S : Type*) [CommRing S] [Algebra R S]
    [IsLocalization.AtPrime S (Ideal.span {f i})] :
    Ring.ord S (algebraMap R S (u * ∏ j ∈ J, f j ^ m j)) = (m i : ℕ∞) := by
  have hL := ord_localization_eq_exponent f hspan hdim J u m i hi
  let e : Localization.AtPrime (Ideal.span {f i}) ≃ₐ[R] S :=
    IsLocalization.algEquiv (Ideal.span {f i}).primeCompl (Localization.AtPrime (Ideal.span {f i})) S
  rw [← e.commutes, ← hL]
  exact ring_ord_ringEquiv_apply e.toRingEquiv _
end ReciprocityTheory.AnForm.R.WMult
