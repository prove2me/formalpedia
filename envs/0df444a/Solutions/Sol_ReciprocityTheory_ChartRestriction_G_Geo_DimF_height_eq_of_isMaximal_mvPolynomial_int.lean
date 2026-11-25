-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.DimF.height_eq_of_isMaximal_mvPolynomial_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:00:00.322015+00:00
-- url     : https://prove2.me/submissions/e02b90e8-1fd3-4d3f-a209-f7341f7b1fb7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_IsCMOfIsRegularLocalRing
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_RingKrullDimLocalizationQuotientEqHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_DimF_height_mvPolynomial_int_fin_of_isMaximal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo.DimF
private theorem ideal_height_eq_order_height_primeSpectrum {R : Type*} [CommRing R] (N : Ideal R) [hN : N.IsPrime] :
    N.height = Order.height (⟨N, hN⟩ : PrimeSpectrum R) := by
  have hmem : N ∈ N.minimalPrimes := by
    rw [Ideal.minimalPrimes_eq_subsingleton_self]; exact Set.mem_singleton N
  unfold Ideal.height
  apply le_antisymm
  · exact iInf₂_le N hmem
  · exact le_iInf₂ fun J hJ =>
      Order.height_mono (show (⟨N, hN⟩ : PrimeSpectrum R) ≤ ⟨J, hJ.1.1⟩ from hJ.1.2)
private theorem order_height_comap_ringEquiv_symm {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (x : PrimeSpectrum A) :
    Order.height (PrimeSpectrum.comap (e.symm : B →+* A) x) = Order.height x := by
  have sm1 : StrictMono (PrimeSpectrum.comap (e.symm : B →+* A)) := by
    intro p q hpq
    refine lt_of_le_of_ne (Ideal.comap_mono hpq.le) ?_
    intro h
    apply hpq.ne
    apply PrimeSpectrum.ext
    exact Ideal.comap_injective_of_surjective _ e.symm.surjective (congrArg PrimeSpectrum.asIdeal h)
  have sm2 : StrictMono (PrimeSpectrum.comap (e : A →+* B)) := by
    intro p q hpq
    refine lt_of_le_of_ne (Ideal.comap_mono hpq.le) ?_
    intro h
    apply hpq.ne
    apply PrimeSpectrum.ext
    exact Ideal.comap_injective_of_surjective _ e.surjective (congrArg PrimeSpectrum.asIdeal h)
  have hcomp : PrimeSpectrum.comap (e : A →+* B) (PrimeSpectrum.comap (e.symm : B →+* A) x) = x := by
    apply PrimeSpectrum.ext
    ext a
    simp
  apply le_antisymm
  · calc Order.height (PrimeSpectrum.comap (e.symm : B →+* A) x)
        ≤ Order.height (PrimeSpectrum.comap (e : A →+* B) (PrimeSpectrum.comap (e.symm : B →+* A) x)) :=
          Order.height_le_height_apply_of_strictMono _ sm2 _
      _ = Order.height x := by rw [hcomp]
  · exact Order.height_le_height_apply_of_strictMono _ sm1 x
end ReciprocityTheory.ChartRestriction.G.Geo.DimF
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.DimF
namespace ReciprocityTheory.ChartRestriction.G.Geo.DimF
theorem _root_.solution {σ : Type*} [Finite σ]
    (M N : Ideal (MvPolynomial σ ℤ)) (hM : M.IsMaximal) (hN : N.IsMaximal) :
    M.height = N.height := by
  obtain ⟨n, ⟨eσ⟩⟩ := Finite.exists_equiv_fin σ
  let e : MvPolynomial σ ℤ ≃+* MvPolynomial (Fin n) ℤ := (MvPolynomial.renameEquiv ℤ eσ).toRingEquiv
  have key : ∀ I : Ideal (MvPolynomial σ ℤ), I.IsMaximal → I.height = n + 1 := by
    intro I hI
    haveI := hI
    haveI := hI.isPrime
    have hJ : (Ideal.comap (e.symm : MvPolynomial (Fin n) ℤ →+* MvPolynomial σ ℤ) I).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ e.symm.surjective
    haveI := hJ.isPrime
    have h1 := height_mvPolynomial_int_fin_of_isMaximal n _ hJ
    rw [ideal_height_eq_order_height_primeSpectrum] at h1 ⊢
    rw [← h1]
    exact (order_height_comap_ringEquiv_symm e _).symm
  rw [key M hM, key N hN]
end ReciprocityTheory.ChartRestriction.G.Geo.DimF
