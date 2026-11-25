-- Prove2me | solution 1 for PI.HtPlacesSumWork.gauss_frac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:50:37.424102+00:00
-- url     : https://prove2.me/submissions/0983a113-445f-4f88-a26e-d7c7338ebd27

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LaTIsPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_PlaceSumHeights_PlaceSumStatements_PlaceSumLemmas_GaussValuationSums_GaussMaximalIdeal
import Theorems.Thm_PI_HtPlacesSumWork_gauss_inj
import Theorems.Thm_PI_HtPlacesSumWork_gauss_lift
import Theorems.Thm_PI_HtPlacesSumWork_gauss_clear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.HtPlacesSumWork
open NumberField IsLocalRing ReciprocityTheory.ChartRestriction.G.T0
variable {K : Type} [Field K] [NumberField K] (D N : ℕ)
  (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
namespace PI.HtPlacesSumWork
theorem _root_.solution :
    letI := (OpToKT D N la).toAlgebra
    IsFractionRing (Op D N la) (KTf K D N) := by
  letI := (ReciprocityTheory.ChartRestriction.G.T0.OpToKT D N la).toAlgebra
  have : IsDomain (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors _)
  have intInj : Function.Injective (ReciprocityTheory.ChartRestriction.G.T0.OTtoKT K D N) :=
    MvPolynomial.map_injective _ (IsFractionRing.injective (𝓞 K) K)
  have fracInj : Function.Injective (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N)) :=
    IsFractionRing.injective (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N)
  have hCinj : ∀ k : 𝓞 K, k ≠ 0 → (MvPolynomial.C k : ReciprocityTheory.ChartRestriction.G.T0.OT K D N) ≠ 0 :=
    fun k hk hC => hk (by simpa using hC)
  have hfinj : Function.Injective (ReciprocityTheory.ChartRestriction.G.T0.OpToKT D N la) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective (ReciprocityTheory.ChartRestriction.G.T0.laT D N la).primeCompl x
    have h1 := congrArg (ReciprocityTheory.ChartRestriction.G.T0.OpToKT D N la)
      (IsLocalization.mk'_spec (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) a t)
    rw [map_mul, hx, zero_mul, gauss_lift] at h1
    have ha : a = 0 := by
      apply intInj
      apply fracInj
      rw [map_zero, map_zero]
      exact h1.symm
    subst ha
    show IsLocalization.mk' (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (0 : ReciprocityTheory.ChartRestriction.G.T0.OT K D N) t = 0
    rw [IsLocalization.mk'_zero]
  refine ⟨fun y => ?_, fun z => ?_, fun {x y} hxy => ?_⟩
  · apply isUnit_iff_ne_zero.mpr
    intro h0
    exact nonZeroDivisors.coe_ne_zero y (hfinj (h0.trans (map_zero _).symm))
  · obtain ⟨P, Q, hQ, rfl⟩ := IsFractionRing.div_surjective (A := ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) z
    obtain ⟨a, n, hn, ha⟩ := gauss_clear D N P
    obtain ⟨b, m, hm, hb⟩ := gauss_clear D N Q
    have hQ0 : Q ≠ 0 := nonZeroDivisors.ne_zero hQ
    have hQ' : algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) Q ≠ 0 :=
      fun h0 => hQ0 (fracInj (h0.trans (map_zero _).symm))
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [map_zero] at hb
      have hc : ReciprocityTheory.ChartRestriction.G.T0.OTtoKT K D N (MvPolynomial.C m) = 0 := by
        rcases mul_eq_zero.mp hb.symm with hc | hc
        · exact hc
        · exact absurd hc hQ0
      exact hCinj m hm (intInj (hc.trans (map_zero _).symm))
    have hden : algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N) (ReciprocityTheory.ChartRestriction.G.T0.Op D N la)
        (b * MvPolynomial.C n) ∈ nonZeroDivisors (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) :=
      mem_nonZeroDivisors_of_ne_zero fun h0 => (mul_ne_zero hb0 (hCinj n hn))
        (gauss_inj D N la (h0.trans (map_zero _).symm))
    refine ⟨⟨algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N) (ReciprocityTheory.ChartRestriction.G.T0.Op D N la)
      (a * MvPolynomial.C m), ⟨_, hden⟩⟩, ?_⟩
    show algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) P /
        algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) Q *
        ReciprocityTheory.ChartRestriction.G.T0.OpToKT D N la (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N)
          (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (b * MvPolynomial.C n)) =
      ReciprocityTheory.ChartRestriction.G.T0.OpToKT D N la (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N)
          (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (a * MvPolynomial.C m))
    rw [gauss_lift, gauss_lift]
    simp only [map_mul, ha, hb]
    rw [div_mul_eq_mul_div, div_eq_iff hQ']
    ring
  · exact ⟨1, by rw [hfinj hxy]⟩
end PI.HtPlacesSumWork
