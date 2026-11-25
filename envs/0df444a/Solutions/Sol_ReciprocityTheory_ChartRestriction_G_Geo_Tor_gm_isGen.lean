-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.gm_isGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:50:11.68493+00:00
-- url     : https://prove2.me/submissions/c7190c66-5ff4-4026-9c42-a9f444919b8c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AdmissibleBasePowerSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleIdentityIso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
variable {X : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {L' L : LB X} {w : LB.Iso L' L} (hw : w.IsGen) {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (j j' : L.ι)
    (k k' : L'.ι) (hj : f y ∈ L.U j) (hj' : f y ∈ L.U j') (hk : f y ∈ L'.U k) (hk' : f y ∈ L'.U k') :
    gv w f y j k = gm f y _ (L.g j j') * (gm f y _ (L'.g k k'))⁻¹ * gv w f y j' k' := by
  have hV : f y ∈ (L.U j ⊓ L'.U k) ⊓ (L.U j' ⊓ L'.U k') := ⟨⟨hj, hk⟩, ⟨hj', hk'⟩⟩
  have hw' : res (inf_le_left : (L.U j ⊓ L'.U k) ⊓ (L.U j' ⊓ L'.U k') ≤ L.U j ⊓ L'.U k) (w.s (j, k)) =
      res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
        (L.U j ⊓ L'.U k) ⊓ (L.U j' ⊓ L'.U k') ≤ L.U j ⊓ L.U j') (L.g j j') *
      (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
        (L.U j ⊓ L'.U k) ⊓ (L.U j' ⊓ L'.U k') ≤ L'.U k ⊓ L'.U k') (L'.g k k'))⁻¹ *
      res (inf_le_right : (L.U j ⊓ L'.U k) ⊓ (L.U j' ⊓ L'.U k') ≤ L.U j' ⊓ L'.U k') (w.s (j', k')) :=
    hw (j, k) (j', k')
  have key := congrArg (gm f y ((L.U j ⊓ L'.U k) ⊓ (L.U j' ⊓ L'.U k'))) hw'
  simp only [map_mul, map_inv, gm_res f y _ hV] at key
  rw [gm_res f y (U := L.U j ⊓ L'.U k) _ hV (w.s (j, k)),
    gm_res f y (U := L.U j' ⊓ L'.U k') _ hV (w.s (j', k'))] at key
  exact key
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
