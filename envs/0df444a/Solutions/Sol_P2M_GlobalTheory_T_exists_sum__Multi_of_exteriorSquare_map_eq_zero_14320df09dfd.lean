-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_sum__Multi_of_exteriorSquare_map_eq_zero_14320df09dfd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:41:49.503489+00:00
-- url     : https://prove2.me/submissions/cfa5a33b-50fe-44a0-8882-cc7c8c3c0a6d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExteriorSquareKerOfSurjective
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExteriorSquareKerOfSurjectiveStatement
import Theorems.Thm_GlobalTheory_exteriorSquare_ker_of_surjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] (W M H : Type) [AddCommGroup W] [Module R W] [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H] (i : W →ₗ[R] M) (p : M →ₗ[R] H), Function.Surjective p → Function.Exact i p → ∀ t : ⋀[R]^2 M, exteriorPower.map 2 p t = 0 → ∃ (n : ℕ) (a : Fin n → M) (w : Fin n → W), t = ∑ k, exteriorPower.ιMulti R 2 ![a k, i (w k)] := by
  first | exact @GlobalTheory.exteriorSquare_ker_of_surjective | exact GlobalTheory.exteriorSquare_ker_of_surjective | (intros; apply GlobalTheory.exteriorSquare_ker_of_surjective <;> assumption)
end _root_.GlobalTheory.T
