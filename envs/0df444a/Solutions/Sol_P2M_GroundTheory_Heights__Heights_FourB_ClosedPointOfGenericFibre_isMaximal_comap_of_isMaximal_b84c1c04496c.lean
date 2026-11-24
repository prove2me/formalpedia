-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_ClosedPointOfGenericFibre_isMaximal_comap_of_isMaximal_b84c1c04496c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:09:24.771978+00:00
-- url     : https://prove2.me/submissions/99c1232a-2dd0-4de3-a372-2813d58a97d3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsClosedPointGenericFibre
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PClosedPointOfGenericFibre
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_int_isJacobsonRing


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
theorem _root_.solution (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R]
    [Algebra (𝓞 F) R] [Algebra.FiniteType (𝓞 F) R] (M : Ideal R) (hM : M.IsMaximal) :
    (M.comap (algebraMap (𝓞 F) R)).IsMaximal := by
  have : IsJacobsonRing ℤ := ReciprocityTheory.ChartRestriction.G.Geo.int_isJacobsonRing
  have : IsJacobsonRing (𝓞 F) := isJacobsonRing_of_isIntegral (R := ℤ)
  let : Field (R ⧸ M) := Ideal.Quotient.field M
  have : Algebra.FiniteType (𝓞 F) (R ⧸ M) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ (𝓞 F) M) (Ideal.Quotient.mkₐ_surjective _ M)
  have : Module.Finite (𝓞 F) (R ⧸ M) := finite_of_finite_type_of_isJacobsonRing (𝓞 F) (R ⧸ M)
  have h := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := 𝓞 F) (⊥ : Ideal (R ⧸ M))
  have he : (⊥ : Ideal (R ⧸ M)).comap (algebraMap (𝓞 F) (R ⧸ M)) =
      M.comap (algebraMap (𝓞 F) R) := by
    ext c
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_bot, ← Ideal.Quotient.mk_algebraMap,
      Ideal.Quotient.eq_zero_iff_mem]
  rwa [he] at h
end GroundTheory.Heights₂.Heights.FourB.ClosedPointOfGenericFibre
