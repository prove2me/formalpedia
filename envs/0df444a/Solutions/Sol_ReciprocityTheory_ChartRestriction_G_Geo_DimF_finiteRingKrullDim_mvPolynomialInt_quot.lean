-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.DimF.finiteRingKrullDim_mvPolynomialInt_quot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:40:12.374145+00:00
-- url     : https://prove2.me/submissions/aa925692-5c92-4b43-a162-ef94945fbb6a

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
theorem _root_.solution {σ : Type*} [Finite σ]
    (P : Ideal (MvPolynomial σ ℤ)) [P.IsPrime] : FiniteRingKrullDim (MvPolynomial σ ℤ ⧸ P) := by
  rw [finiteRingKrullDim_iff_ne_bot_and_top]
  refine ⟨fun hb => ?_, ?_⟩
  · have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial σ ℤ ⧸ P)
    rw [hb] at h0
    exact absurd h0 (by simp)
  refine ne_top_of_le_ne_top ?_ (ringKrullDim_quotient_le P)
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
    IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
  rw [← Nat.cast_one, ← Nat.cast_add]
  rw [← WithBot.coe_natCast]
  exact ne_of_lt (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _))
end ReciprocityTheory.ChartRestriction.G.Geo.DimF
