-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_finset_model_of_isAffine__8386d6febae7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:34:31.602883+00:00
-- url     : https://prove2.me/submissions/a0617e30-4309-44dd-830f-eb1b65c038c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFinsetModelOfIsAffine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFinsetModelOfIsAffineStatement
import Theorems.Thm_GlobalTheory_exists_finset_model_of_isAffine


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] (X : Over (Sp K)), IsAffine X.left → LocallyOfFiniteType X.hom → ∃ s : Finset K, ∀ (k : Type) [Field k] (β : k →+* K), (s : Set K) ⊆ Set.range β → ∃ (X₀ : Over (Sp k)) (φ : X.left ⟶ X₀.left), IsPullback φ X.hom X₀.hom (spMap β) := by
  first | exact @GlobalTheory.exists_finset_model_of_isAffine | exact GlobalTheory.exists_finset_model_of_isAffine | (intros; apply GlobalTheory.exists_finset_model_of_isAffine <;> assumption)
end _root_.GlobalTheory.T
