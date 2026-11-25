-- Prove2me | solution 1 for P2M_GlobalTheory_GlueLineBundle_gm_glue_g__18e2be52006f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:56:53.789979+00:00
-- url     : https://prove2.me/submissions/664a0584-4e4a-400c-83d2-253d0d982af0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GlueLineBundles
import Theorems.Thm_GlobalTheory_GlueLineBundle_gm_glue_g

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.GlueLineBundle
variable {X : Scheme.{0}} {A : Type} (V : A → X.Opens) (M : ∀ a, LB (V a).toScheme)
namespace GlobalTheory.GlueLineBundle
theorem _root_.solution (a : A) (w : (V a).toScheme) (i k : (M a).ι)
    (hi : w ∈ (M a).U i) (hk : w ∈ (M a).U k) :
    gm (V a).ι w _ ((glue V M).g ⟨a, i⟩ ⟨a, k⟩) = gm (𝟙 _) w ((M a).U i ⊓ (M a).U k) ((M a).g i k) := by
  have := gm_glue_g V M a (𝟙 _) w i k hi hk
  rwa [Category.id_comp] at this
end GlobalTheory.GlueLineBundle
