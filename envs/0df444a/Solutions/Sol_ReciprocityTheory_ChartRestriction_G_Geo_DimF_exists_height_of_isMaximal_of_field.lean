-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.DimF.exists_height_of_isMaximal_of_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:06:16.223626+00:00
-- url     : https://prove2.me/submissions/95bb1ae5-b7cf-416e-ab5f-eadf38b22dd5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_DimF_height_mvPolynomial_fin_of_isMaximal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_DimF_height_map_under_eq_zero

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
open Ideal
namespace ReciprocityTheory.ChartRestriction.G.Geo.DimF
theorem _root_.solution (k B : Type*) [Field k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B] :
    ∃ s : ℕ, ∀ M : Ideal B, M.IsMaximal → M.height = s := by
  classical
  obtain ⟨s, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k B
  letI : Algebra (MvPolynomial (Fin s) k) B := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin s) k) B := hfin
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) B := Algebra.IsIntegral.of_finite _ _
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) B := (faithfulSMul_iff_algebraMap_injective _ _).2 hg
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  refine ⟨s, fun M hM => ?_⟩
  haveI := hM
  haveI hmax : (M.under (MvPolynomial (Fin s) k)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
  haveI : M.LiesOver (M.under (MvPolynomial (Fin s) k)) := ⟨rfl⟩
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (M.under (MvPolynomial (Fin s) k)) M,
    height_mvPolynomial_fin_of_isMaximal s _ hmax, height_map_under_eq_zero M, add_zero]
end ReciprocityTheory.ChartRestriction.G.Geo.DimF
