-- Prove2me | solution 1 for ReciprocityTheory.CA.height_eq_of_isMaximal_of_trdeg_eq_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:06:47.99485+00:00
-- url     : https://prove2.me/submissions/10770fc0-5d34-4942-884e-b408aeb528f1

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolyCM
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Theorems.Thm_ReciprocityTheory_CA_height_add_height_maximal_quotient_field
import Theorems.Thm_ReciprocityTheory_CA_height_add_ringKrullDim_quotient_mvPolynomial_field
import Theorems.Thm_ReciprocityTheory_CA_ringKrullDim_eq_of_trdeg_eq_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
universe u
namespace ReciprocityTheory.CA
theorem _root_.solution {K A : Type u} [Field K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] (n : ℕ) (h : Algebra.trdeg K A = n) (𝔪 : Ideal A)
    [𝔪.IsMaximal] : 𝔪.height = n := by
  obtain ⟨N, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType K A)
  let e : (MvPolynomial (Fin N) K ⧸ RingHom.ker f.toRingHom) ≃+* A :=
    RingHom.quotientKerEquivOfSurjective (f := f.toRingHom) hf
  haveI : (RingHom.ker f.toRingHom).IsPrime := RingHom.ker_isPrime _
  haveI : (𝔪.comap e).IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.surjective
  have h5 := height_add_height_maximal_quotient_field K N (RingHom.ker f.toRingHom) (𝔪.comap e)
  rw [RingEquiv.height_comap] at h5
  have h6 := height_add_ringKrullDim_quotient_mvPolynomial_field K N (RingHom.ker f.toRingHom)
  rw [ringKrullDim_eq_of_ringEquiv e, ringKrullDim_eq_of_trdeg_eq_field n h] at h6
  have h6' : (RingHom.ker f.toRingHom).height + n = N := by exact_mod_cast h6
  have cancel : ∀ a b : ℕ∞, (RingHom.ker f.toRingHom).height + a = N → (RingHom.ker f.toRingHom).height + b = N → a = b := by
      intro a b ha hb
      have hq : (RingHom.ker f.toRingHom).height ≠ ⊤ := fun h => by rw [h, top_add] at ha; exact ENat.top_ne_coe N ha
      have ha' : a ≠ ⊤ := fun h => by rw [h, add_top] at ha; exact ENat.top_ne_coe N ha
      have hb' : b ≠ ⊤ := fun h => by rw [h, add_top] at hb; exact ENat.top_ne_coe N hb
      obtain ⟨q, hq0⟩ := ENat.ne_top_iff_exists.1 hq
      obtain ⟨a0, ha0⟩ := ENat.ne_top_iff_exists.1 ha'
      obtain ⟨b0, hb0⟩ := ENat.ne_top_iff_exists.1 hb'
      rw [← hq0, ← ha0] at ha
      rw [← hq0, ← hb0] at hb
      rw [← ha0, ← hb0]
      have e1 : q + a0 = N := by exact_mod_cast ha
      have e2 : q + b0 = N := by exact_mod_cast hb
      congr 1
      omega
  exact cancel _ _ h5 h6'
end ReciprocityTheory.CA
