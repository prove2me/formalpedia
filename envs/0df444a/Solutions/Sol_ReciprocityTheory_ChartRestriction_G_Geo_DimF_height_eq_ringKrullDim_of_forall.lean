-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.DimF.height_eq_ringKrullDim_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:32.873803+00:00
-- url     : https://prove2.me/submissions/20bba48d-e79c-4b0d-a384-10f82f0c370f

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
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.DimF
namespace ReciprocityTheory.ChartRestriction.G.Geo.DimF
theorem _root_.solution {B : Type*} [CommRing B]
    (hB : ∀ M N : Ideal B, M.IsMaximal → N.IsMaximal → M.height = N.height)
    (M : Ideal B) (hM : M.IsMaximal) : (M.height : WithBot ℕ∞) = ringKrullDim B := by
  haveI := hM.isPrime
  apply le_antisymm
  · exact Ideal.height_le_ringKrullDim_of_ne_top hM.ne_top
  · rw [ringKrullDim, Order.krullDim_eq_iSup_height]
    refine iSup_le fun p => ?_
    obtain ⟨N, hN, hpN⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
    haveI := hN.isPrime
    have h1 : Order.height p ≤ Order.height (⟨N, hN.isPrime⟩ : PrimeSpectrum B) :=
      Order.height_mono (show p ≤ ⟨N, hN.isPrime⟩ from hpN)
    have h2 : N.height = Order.height (⟨N, hN.isPrime⟩ : PrimeSpectrum B) := by
      have hmem : N ∈ N.minimalPrimes := by
        rw [Ideal.minimalPrimes_eq_subsingleton_self]; exact Set.mem_singleton N
      unfold Ideal.height
      apply le_antisymm
      · exact iInf₂_le N hmem
      · exact le_iInf₂ fun J hJ =>
          Order.height_mono (show (⟨N, hN.isPrime⟩ : PrimeSpectrum B) ≤ ⟨J, hJ.1.1⟩ from hJ.1.2)
    rw [hB M N hM hN, h2]
    exact_mod_cast h1
end ReciprocityTheory.ChartRestriction.G.Geo.DimF
