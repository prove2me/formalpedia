-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.chart_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:31:53.15371+00:00
-- url     : https://prove2.me/submissions/72b8fa0e-bdea-4e8f-9685-dbc19bf20c4e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TanLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ChartAway
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_one_left__f4b8b6e904c4
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] (G : Over (Spec (CommRingCat.of S))) [GrpObj G]
set_option backward.isDefEq.respectTransparency.types false
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution (U : G.left.Opens) (hU : IsAffineOpen U) (s : S)
    (hs : ∀ x : Spec (CommRingCat.of S), s ∉ x.asIdeal → (η[G]).left x ∈ U) : Nonempty (Chart (Gs G s)) := by
  have hP := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback G (fB S (Localization.Away s))
  have key : (η[Gs G s]).left ≫ pullback.fst G.hom (fB S (Localization.Away s)) =
      fB S (Localization.Away s) ≫ (η[G]).left := by
    have h1 := congrArg (fun m => m.left)
      (map_one (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hP
        (Over.mk (𝟙 (Spec (CommRingCat.of (Localization.Away s)))))))
    simp only [one_left'] at h1
    change (1 : Over.mk (𝟙 (Spec (CommRingCat.of (Localization.Away s)))) ⟶ Gs G s).left ≫
      pullback.fst G.hom (fB S (Localization.Away s)) = _ at h1
    rw [one_left'] at h1
    simpa using h1
  have hs' : ∀ y : Spec (CommRingCat.of (Localization.Away s)),
      s ∉ ((fB S (Localization.Away s)).base y).asIdeal := by
    intro y hy
    have hu : IsUnit (algebraMap S (Localization.Away s) s) :=
      IsLocalization.Away.algebraMap_isUnit s
    have hmem : algebraMap S (Localization.Away s) s ∈ y.asIdeal := hy
    exact y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu)
  haveI hf : IsAffineHom (fB S (Localization.Away s)) := inferInstance
  haveI : IsAffineHom (pullback.fst G.hom (fB S (Localization.Away s))) :=
    MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ hf
  refine ⟨⟨pullback.fst G.hom (fB S (Localization.Away s)) ⁻¹ᵁ U, hU.preimage _, ?_⟩⟩
  intro y _
  have hk : (pullback.fst G.hom (fB S (Localization.Away s))).base ((η[Gs G s]).left.base y) =
      (η[G]).left.base ((fB S (Localization.Away s)).base y) := by
    change ((η[Gs G s]).left ≫ pullback.fst G.hom (fB S (Localization.Away s))).base y =
      (fB S (Localization.Away s) ≫ (η[G]).left).base y
    rw [key]
  show (pullback.fst G.hom (fB S (Localization.Away s))).base ((η[Gs G s]).left.base y) ∈ U
  rw [hk]
  exact hs _ (hs' y)
end ReciprocityTheory.ChartRestriction.G.Chart
