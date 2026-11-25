-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.DimF.height_int_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:23:29.745209+00:00
-- url     : https://prove2.me/submissions/5201185c-6555-40d1-b3b7-36b28be6f66b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_IsCMOfIsRegularLocalRing
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_RingKrullDimLocalizationQuotientEqHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAB
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
end ReciprocityTheory.ChartRestriction.G.Geo.DimF
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.DimF
namespace ReciprocityTheory.ChartRestriction.G.Geo.DimF
theorem _root_.solution (M : Ideal ℤ) (hM : M.IsMaximal) : M.height = 1 := by
  haveI := hM.isPrime
  rw [ideal_height_eq_order_height_primeSpectrum M]
  have hMbot : M ≠ ⊥ := by
    intro h
    subst h
    exact Int.not_isField (Ring.isField_iff_maximal_bot.mpr hM)
  have hmin : ∀ z : PrimeSpectrum ℤ, z < ⟨M, hM.isPrime⟩ → IsMin z := by
    intro z hz
    have hz' : z.asIdeal < M := hz
    have hz0 : z.asIdeal = ⊥ := by
      by_contra hne
      have hmax : z.asIdeal.IsMaximal := by
        first
          | exact z.isPrime.isMaximal hne
          | exact Ring.DimensionLEOne.maximalOfPrime hne z.isPrime
          | exact Ideal.IsPrime.to_maximal_ideal z.isPrime hne
      exact (ne_of_lt hz') (hmax.eq_of_le hM.ne_top (le_of_lt hz'))
    intro w _
    show z.asIdeal ≤ w.asIdeal
    rw [hz0]
    exact bot_le
  have hx : ¬ IsMin (⟨M, hM.isPrime⟩ : PrimeSpectrum ℤ) := by
    intro h
    have hlt : (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum ℤ) < ⟨M, hM.isPrime⟩ :=
      show (⊥ : Ideal ℤ) < M from bot_lt_iff_ne_bot.mpr hMbot
    exact lt_irrefl _ (lt_of_lt_of_le hlt (h (le_of_lt hlt)))
  apply le_antisymm
  · first
      | (rw [Order.height_eq_iSup_lt_height]
         refine iSup₂_le fun z hz => ?_
         rw [Order.height_eq_zero.mpr (hmin z hz)]
         simp)
      | (show Order.height _ ≤ ((1 : ℕ) : ℕ∞)
         rw [Order.height_le_coe_iff]
         intro z hz
         rw [Order.height_eq_zero.mpr (hmin z hz)]
         exact zero_lt_one)
  · first
      | exact Order.one_le_height_iff.mpr hx
      | exact ENat.one_le_iff_ne_zero.mpr (fun h0 => hx (Order.height_eq_zero.mp h0))
end ReciprocityTheory.ChartRestriction.G.Geo.DimF
