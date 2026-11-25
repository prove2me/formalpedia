-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.ringKrullDim_locAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:12:12.285718+00:00
-- url     : https://prove2.me/submissions/e7c7af60-4f60-44c0-938c-317038231db7

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartA
import Theorems.Thm_ReciprocityTheory_AnForm_R_ptIdealOf_isMaximal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial Algebra
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {σ : Type} (J : Ideal (MvPolynomial σ ℂ)) (z : σ → ℂ)
    (hJ : J ≤ ptIdealOf z) :
    ringKrullDim (locAt J z) = ((ptIdealOf z).map (Ideal.Quotient.mk J)).height := by
  haveI hm : (ptIdealOf z).IsPrime := (ptIdealOf_isMaximal z).isPrime
  have hmem : ∀ a : MvPolynomial σ ℂ,
      Ideal.Quotient.mk J a ∈ (ptIdealOf z).map (Ideal.Quotient.mk J) ↔ a ∈ ptIdealOf z :=
    fun a => Ideal.mem_quotient_iff_mem hJ
  haveI hm' : ((ptIdealOf z).map (Ideal.Quotient.mk J)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hJ)
  haveI : IsLocalization.AtPrime (locAt J z) ((ptIdealOf z).map (Ideal.Quotient.mk J)) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨r, hr⟩
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
      have hr' : Ideal.Quotient.mk J a ∉ (ptIdealOf z).map (Ideal.Quotient.mk J) := hr
      have ha : a ∉ ptIdealOf z := fun h => hr' ((hmem a).2 h)
      exact (IsLocalization.map_units (Localization.AtPrime (ptIdealOf z))
        (⟨a, ha⟩ : (ptIdealOf z).primeCompl)).map (Ideal.Quotient.mk _)
    · intro w
      obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective w
      obtain ⟨⟨a, s⟩, hu⟩ := IsLocalization.surj (ptIdealOf z).primeCompl u
      have hs' : (s : MvPolynomial σ ℂ) ∉ ptIdealOf z := s.2
      have hs : Ideal.Quotient.mk J (s : MvPolynomial σ ℂ) ∉ (ptIdealOf z).map (Ideal.Quotient.mk J) :=
        fun h => hs' ((hmem _).1 h)
      refine ⟨(Ideal.Quotient.mk J a, ⟨Ideal.Quotient.mk J s, hs⟩), ?_⟩
      show Ideal.Quotient.mk _ u *
          Ideal.Quotient.mk _ (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (ptIdealOf z)) s) =
        Ideal.Quotient.mk _ (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (ptIdealOf z)) a)
      rw [← map_mul]
      exact congrArg (Ideal.Quotient.mk _) hu
    · intro x y hxy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      have hxy' : Ideal.Quotient.mk (J.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (ptIdealOf z))))
            (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (ptIdealOf z)) a) =
          Ideal.Quotient.mk _ (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (ptIdealOf z)) b) := hxy
      have h1 := Ideal.Quotient.eq.1 hxy'
      rw [← map_sub] at h1
      obtain ⟨⟨i, s⟩, hs⟩ :=
        (IsLocalization.mem_map_algebraMap_iff (ptIdealOf z).primeCompl
          (Localization.AtPrime (ptIdealOf z))).1 h1
      rw [← map_mul, IsLocalization.eq_iff_exists (ptIdealOf z).primeCompl] at hs
      obtain ⟨c, hc⟩ := hs
      have hc' : (c : MvPolynomial σ ℂ) ∉ ptIdealOf z := c.2
      have hs' : (s : MvPolynomial σ ℂ) ∉ ptIdealOf z := s.2
      have hcs : (c : MvPolynomial σ ℂ) * s ∉ ptIdealOf z := fun h => (hm.mem_or_mem h).elim hc' hs'
      refine ⟨⟨Ideal.Quotient.mk J ((c : MvPolynomial σ ℂ) * s), fun h => hcs ((hmem _).1 h)⟩, ?_⟩
      show Ideal.Quotient.mk J ((c : MvPolynomial σ ℂ) * s) * Ideal.Quotient.mk J a =
        Ideal.Quotient.mk J ((c : MvPolynomial σ ℂ) * s) * Ideal.Quotient.mk J b
      rw [← map_mul, ← map_mul, Ideal.Quotient.eq]
      have e : (c : MvPolynomial σ ℂ) * s * a - c * s * b = c * i := by
        linear_combination hc
      rw [e]
      exact J.mul_mem_left _ i.2
  exact IsLocalization.AtPrime.ringKrullDim_eq_height _ (locAt J z)
end ReciprocityTheory.AnForm.R
