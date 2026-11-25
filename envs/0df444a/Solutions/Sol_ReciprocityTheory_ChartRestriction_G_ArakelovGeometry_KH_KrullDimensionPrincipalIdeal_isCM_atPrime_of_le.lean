-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KrullDimensionPrincipalIdeal.isCM_atPrime_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:09:47.516951+00:00
-- url     : https://prove2.me/submissions/b93d9f3f-6c8a-42f4-8c46-7a4347a898bd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDimSt
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_WeakRegularity_RingKrullDimQuotientAddOneLeOfLt
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_LocDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Bridge
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_DimFormulaOfSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDimA
import Theorems.Thm_ReciprocityTheory_CA_DepthGE_of_ringEquiv
import Theorems.Thm_ReciprocityTheory_CA_IsCM_localization_atPrime
import Theorems.Thm_ReciprocityTheory_CA_IsCM_of_ringEquiv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KrullDimensionPrincipalIdeal
open ReciprocityTheory.CA
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KrullDimensionPrincipalIdeal
theorem _root_.solution {S : Type*} [CommRing S] (𝔐 W : Ideal S) [𝔐.IsPrime] [W.IsPrime]
    (h : IsCM (Localization.AtPrime 𝔐)) (hle : W ≤ 𝔐) : IsCM (Localization.AtPrime W) := by
  have hdisj : Disjoint (𝔐.primeCompl : Set S) (W : Set S) :=
    Set.disjoint_left.mpr fun x hx hxp => hx (hle hxp)
  let p := W.map (algebraMap S (Localization.AtPrime 𝔐))
  have : p.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint 𝔐.primeCompl _ W inferInstance hdisj
  have hc : p.comap (algebraMap S (Localization.AtPrime 𝔐)) = W :=
    IsLocalization.under_map_of_isPrime_disjoint 𝔐.primeCompl _ (I := W) inferInstance hdisj
  have h2 := h.localization_atPrime p
  have : IsLocalization W.primeCompl (Localization.AtPrime p) := by
    have h0 : IsLocalization (p.comap (algebraMap S (Localization.AtPrime 𝔐))).primeCompl
        (Localization.AtPrime p) := inferInstance
    convert h0 using 2
    rw [hc]
  let e := IsLocalization.algEquiv W.primeCompl (Localization.AtPrime W) (Localization.AtPrime p)
  exact h2.of_ringEquiv e.symm.toRingEquiv
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KrullDimensionPrincipalIdeal
