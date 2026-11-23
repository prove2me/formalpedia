-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.regVert_valuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:37:11.961176+00:00
-- url     : https://prove2.me/submissions/738bd1b8-2442-45e7-90d0-72cf19b61f77

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegAVpt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegVert
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_regVert_eq_of_le_height_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open IsLocalRing
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (P : Ideal A) [P.IsPrime] (hP : P.height = 1) :
    ValuationRing (Localization.AtPrime P) := by
  have hPne : P ≠ ⊥ := by
    rintro rfl
    have h0 : (⊥ : Ideal A).height = 0 := by
      first
      | exact Ideal.height_bot
      | simp
    rw [h0] at hP
    exact zero_ne_one hP
  haveI : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  have hinj : Function.Injective (algebraMap A (Localization.AtPrime P)) :=
    IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors
  have hmax : Ideal.map (algebraMap A (Localization.AtPrime P)) P =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) :=
    Localization.AtPrime.map_eq_maximalIdeal
  have hcm : Ideal.comap (algebraMap A (Localization.AtPrime P))
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) = P := by
    first
    | exact Localization.AtPrime.comap_maximalIdeal
    | exact IsLocalization.AtPrime.comap_maximalIdeal _ P
  have hmne : IsLocalRing.maximalIdeal (Localization.AtPrime P) ≠ ⊥ := by
    rw [← hmax]
    intro h
    exact hPne ((Ideal.map_eq_bot_iff_of_injective hinj).mp h)
  have hnf : ¬ IsField (Localization.AtPrime P) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq]
    exact hmne
  haveI : IsDomain (Localization.AtPrime P) := by
    first
    | infer_instance
    | exact IsLocalization.isDomain_localization P.primeCompl_le_nonZeroDivisors
  haveI hic : IsIntegrallyClosed (Localization.AtPrime P) := by
    first
    | exact isIntegrallyClosed_of_isLocalization P.primeCompl P.primeCompl_le_nonZeroDivisors
    | exact isIntegrallyClosed_of_isLocalization (S := Localization.AtPrime P) P.primeCompl
        P.primeCompl_le_nonZeroDivisors
    | exact IsIntegrallyClosed.of_isLocalization (Localization.AtPrime P) P.primeCompl
        P.primeCompl_le_nonZeroDivisors
    | exact isIntegrallyClosed_of_isLocalization (Localization.AtPrime P) P.primeCompl
        P.primeCompl_le_nonZeroDivisors
  have huniq : ∃! Q' : Ideal (Localization.AtPrime P), Q' ≠ ⊥ ∧ Q'.IsPrime := by
    refine ⟨IsLocalRing.maximalIdeal _, ⟨hmne, inferInstance⟩, ?_⟩
    rintro Q' ⟨hQ'ne, hQ'p⟩
    haveI := hQ'p
    have hc : Q'.under A ≤ P := by
      exact (Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQ'p.ne_top)).trans hcm.le
    have hcne : Q'.under A ≠ ⊥ := by
      intro h
      apply hQ'ne
      rw [← IsLocalization.map_comap P.primeCompl (Localization.AtPrime P) Q', h, Ideal.map_bot]
    have heq := regVert_eq_of_le_height_one hcne hc hP
    rw [← IsLocalization.map_comap P.primeCompl (Localization.AtPrime P) Q', heq, hmax]
  first
  | exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 3).mpr (And.intro hic huniq)
  | exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 4).mpr (And.intro hic huniq)
  | exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 2).mpr (And.intro hic huniq)
  | exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 5).mpr (And.intro hic huniq)
  | exact @ValuationRing.of_isDiscreteValuationRing _ _ _ (((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 0 3).mpr (And.intro hic huniq))
  | exact @ValuationRing.of_isDiscreteValuationRing _ _ _ (((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 0 4).mpr (And.intro hic huniq))
  | exact @ValuationRing.of_isDiscreteValuationRing _ _ _ (((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 0 2).mpr (And.intro hic huniq))
  | exact @ValuationRing.of_isDiscreteValuationRing _ _ _ (((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 0 5).mpr (And.intro hic huniq))
  | exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 2 3).mpr (And.intro hic huniq)
  | exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 2 4).mpr (And.intro hic huniq)
  | exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 2 5).mpr (And.intro hic huniq)
end ReciprocityTheory.ChartRestriction.G.T0
