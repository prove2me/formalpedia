-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.transL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:05:09.039071+00:00
-- url     : https://prove2.me/submissions/10e7851c-de99-47b5-9992-9dce077af5f6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pullU_res__268497da66fb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
variable {S : Scheme.{0}} {E : SplitExt S} {G₁ G₂ : Over S} [GrpObj G₁] [GrpObj G₂]
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {B Y Z : Scheme.{0}} (a : Z ⟶ Y) (q : Y ⟶ B) (U U' : B.Opens) (g : Γ(B, U ⊓ U')ˣ)
    (u : Γ(Y, q ⁻¹ᵁ U)ˣ) (u' : Γ(Y, q ⁻¹ᵁ U')ˣ)
    (h : res (q.preimage_mono (inf_le_right : U ⊓ U' ≤ U')) u' =
      pullU q _ g * res (q.preimage_mono (inf_le_left : U ⊓ U' ≤ U)) u) :
    res (a.preimage_mono (q.preimage_mono (inf_le_right : U ⊓ U' ≤ U'))) (pullU a _ u') =
      pullU a _ (pullU q _ g) * res (a.preimage_mono (q.preimage_mono (inf_le_left : U ⊓ U' ≤ U))) (pullU a _ u) := by
  have := congrArg (pullU a _) h
  rw [map_mul, pullU_res₂, pullU_res₂] at this
  exact this
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
