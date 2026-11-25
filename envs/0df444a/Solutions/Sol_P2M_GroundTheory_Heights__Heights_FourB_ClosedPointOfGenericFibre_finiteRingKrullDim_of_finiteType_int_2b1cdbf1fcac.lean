-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_ClosedPointOfGenericFibre_finiteRingKrullDim_of_finiteType_int_2b1cdbf1fcac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:29:45.557939+00:00
-- url     : https://prove2.me/submissions/ef1fc4d8-4e7b-4de1-ac3d-88dc3ae273ba

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsClosedPointGenericFibre
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PClosedPointOfGenericFibre
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_DimF_finiteRingKrullDim_mvPolynomialInt_quot


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open IsDedekindDomain NumberField
open GroundTheory.Heights₂.Heights.FourB.ClosedPointOfGenericFibre
namespace GroundTheory.Heights₂.Heights.FourB.ClosedPointOfGenericFibre
theorem _root_.solution (R : Type) [CommRing R] [IsDomain R]
    [Algebra.FiniteType ℤ R] : FiniteRingKrullDim R := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType ℤ R›
  have : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  have h := ReciprocityTheory.ChartRestriction.G.Geo.DimF.finiteRingKrullDim_mvPolynomialInt_quot (RingHom.ker f)
  let e := (Ideal.quotientKerAlgEquivOfSurjective hf).toRingEquiv
  rw [finiteRingKrullDim_iff_ne_bot_and_top, ← ringKrullDim_eq_of_ringEquiv e]
  exact finiteRingKrullDim_iff_ne_bot_and_top.mp h
end GroundTheory.Heights₂.Heights.FourB.ClosedPointOfGenericFibre
