-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_finiteType_model_of_smooth_affine__3a72afc0280b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:21:27.018801+00:00
-- url     : https://prove2.me/submissions/8693e1fd-456d-4466-953a-743e61916cb7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteTypeModelOfSmoothAffine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteTypeModelOfSmoothAffineStatement
import Theorems.Thm_GlobalTheory_exists_finiteType_model_of_smooth_affine


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V : Type) [CommRing V] (X : Scheme.{0}) (p : X ⟶ Sp V), IsAffine X → Smooth p → ∃ (R : Type) (_ : CommRing R) (f : R →+* V) (X₀ : Scheme.{0}) (p₀ : X₀ ⟶ Sp R) (φ : X ⟶ X₀), Algebra.FiniteType ℤ R ∧ Smooth p₀ ∧ IsAffine X₀ ∧ IsPullback φ p p₀ (spMap f) := by
  first | exact @GlobalTheory.exists_finiteType_model_of_smooth_affine | exact GlobalTheory.exists_finiteType_model_of_smooth_affine | (intros; apply GlobalTheory.exists_finiteType_model_of_smooth_affine <;> assumption)
end _root_.GlobalTheory.T
