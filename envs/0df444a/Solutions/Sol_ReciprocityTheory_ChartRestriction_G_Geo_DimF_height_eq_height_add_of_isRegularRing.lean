-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.DimF.height_eq_height_add_of_isRegularRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:46:03.930236+00:00
-- url     : https://prove2.me/submissions/45eb2400-944e-46a0-8f81-daa92f06495c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_IsCMOfIsRegularLocalRing
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_RingKrullDimLocalizationQuotientEqHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAB
import Theorems.Thm_ReciprocityTheory_CA_IsCM_height_add_ringKrullDim_quotient
import Theorems.Thm_ReciprocityTheory_CA_isCM_of_isRegularLocalRing
import Theorems.Thm_ReciprocityTheory_CA_ringKrullDim_localization_quotient_eq_height


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
theorem _root_.solution {R : Type*} [CommRing R] [IsRegularRing R]
    (p q : Ideal R) [p.IsPrime] [q.IsPrime] (hpq : p ≤ q) :
    q.height = p.height + (q.map (Ideal.Quotient.mk p)).height := by
  have hA : ReciprocityTheory.CA.IsCM (Localization.AtPrime q) :=
    ReciprocityTheory.CA.isCM_of_isRegularLocalRing _
  have hdisj : Disjoint (q.primeCompl : Set R) (p : Set R) :=
    Set.disjoint_left.mpr fun x hx hxp => hx (hpq hxp)
  have : (p.map (algebraMap R (Localization.AtPrime q))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ p inferInstance hdisj
  have e := hA.height_add_ringKrullDim_quotient (p.map (algebraMap R (Localization.AtPrime q)))
  rw [IsLocalization.height_map_of_disjoint q.primeCompl p hdisj,
    ReciprocityTheory.CA.ringKrullDim_localization_quotient_eq_height p q hpq,
    IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)] at e
  exact_mod_cast e.symm
end ReciprocityTheory.ChartRestriction.G.Geo.DimF
