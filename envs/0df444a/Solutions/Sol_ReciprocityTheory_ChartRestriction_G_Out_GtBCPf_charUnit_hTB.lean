-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.charUnit_hTB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:34:20.580221+00:00
-- url     : https://prove2.me/submissions/8f715510-f238-4e8d-95c9-71adaa3c3b86

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_PreLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_UnitsEq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_gmRP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_unit_ext


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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
open Semi Geo.Tor PullGtPf
variable {S S' : Scheme.{0}} (f : S' ⟶ S) (X : Type) [AddCommGroup X]
namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
theorem _root_.solution (χ : X) :
    res (fun _ _ => trivial : (⊤ : (splitTorus S' X).left.Opens) ≤ hT f X ⁻¹ᵁ ⊤)
      (pullU (hT f X) ⊤ (charUnit S X χ)) = charUnit S' X χ := by
  let w := Units.map (Scheme.ΓSpecIso (torusRing ZU X)).inv.hom.toMonoidHom
    (Units.map (AddMonoidAlgebra.of ZU X) (toUnits (Multiplicative.ofAdd χ)))
  refine unit_ext fun x _ => ?_
  have e3 : hT f X ≫ pullback.fst (splitTorusAff ZU X).hom (toZ S) =
      pullback.fst (splitTorusAff ZU X).hom (toZ S') := pullback.lift_fst _ _ _
  have e1 : gm (𝟙 _) x ⊤ (charUnit S' X χ) =
      gm (pullback.fst (splitTorusAff ZU X).hom (toZ S')) x ⊤ w :=
    gmRP (pullback.fst (splitTorusAff ZU X).hom (toZ S')) x ⊤ ⊤ _ trivial w
  have e2 : gm (hT f X) x ⊤ (charUnit S X χ) =
      gm (hT f X ≫ pullback.fst (splitTorusAff ZU X).hom (toZ S)) x ⊤ w :=
    (gm_res (hT f X) x (V := ⊤) (U := pullback.fst (splitTorusAff ZU X).hom (toZ S) ⁻¹ᵁ ⊤) _
      trivial _).trans (gm_pull _ _ x ⊤ trivial w)
  rw [e3] at e2
  exact (gmRP (hT f X) x ⊤ ⊤ _ trivial _).trans (e2.trans e1.symm)
end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
