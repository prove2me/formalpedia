-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.gm_maps_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:00:44.535391+00:00
-- url     : https://prove2.me/submissions/c9dee09c-e33b-4b05-ab22-ce4828e1511e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AdmissibleBasePowerSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleIdentityIso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
section Bundles
variable {X : Scheme.{0}}
private theorem gm_pullU_eq_gm_comp {X Y Z : Scheme.{0}} (φ : Y ⟶ X) (r : Z ⟶ Y) (z : Z) {U : X.Opens}
    (h : φ (r z) ∈ U) (x : Γ(X, U)ˣ) :
    gm r z (φ ⁻¹ᵁ U) (pullU φ U x) = gm (r ≫ φ) z U x := by
  have h₁ : r z ∈ φ ⁻¹ᵁ U := h
  have h₂ : (r ≫ φ) z ∈ U := h
  simp only [gm, dif_pos h₁, dif_pos h₂, MonoidHom.comp_apply]
  ext
  simp only [Units.coe_map, pullU, MonoidHom.coe_coe]
  first
    | rfl
    | (rw [Scheme.comp_app]; rfl)
end Bundles
section Unif
open ReciprocityTheory.ChartRestriction.G.Out
end Unif
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
variable {X : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {L' L : LB X} {w : LB.Iso L' L} {Y : Scheme.{0}} {φ : Y ⟶ X} {a : LB.Gen (L'.pull φ)}
    {b : LB.Gen (L.pull φ)} (h : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => φ) (fun _ => 1)) a b)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (p : L.ι) (q : L'.ι) (hp : φ (r z) ∈ L.U p) (hq : φ (r z) ∈ L'.U q) :
    gm r z _ (b.s (fun _ => p)) = gv w (r ≫ φ) z p q * gm r z _ (a.s (fun _ => q)) := by
  have hV : r z ∈ LB.wchart L (fun _ => φ) (fun _ => p) ⊓ LB.wchart L' (fun _ => φ) (fun _ => q) :=
    ⟨mem_pull.2 hp, mem_pull.2 hq⟩
  have h' : res (U := LB.wchart L (fun _ => φ) (fun _ => p))
        (V := LB.wchart L (fun _ => φ) (fun _ => p) ⊓ LB.wchart L' (fun _ => φ) (fun _ => q)) inf_le_left
        (b.s (fun _ => p)) =
      (∏ _k : PUnit, (res (U := φ ⁻¹ᵁ (L.U p ⊓ L'.U q))
          (V := LB.wchart L (fun _ => φ) (fun _ => p) ⊓ LB.wchart L' (fun _ => φ) (fun _ => q))
          (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ => φ) (fun _ => p) PUnit.unit))
            (inf_le_right.trans (LB.wchart_le L' (fun _ => φ) (fun _ => q) PUnit.unit)))
          (pullU φ (L.U p ⊓ L'.U q) (w.s (p, q)))) ^ (1 : ℤ)) *
      res (U := LB.wchart L' (fun _ => φ) (fun _ => q))
        (V := LB.wchart L (fun _ => φ) (fun _ => p) ⊓ LB.wchart L' (fun _ => φ) (fun _ => q)) inf_le_right
        (a.s (fun _ => q)) :=
    h (fun _ => p, fun _ => q)
  rw [Fintype.prod_unique, zpow_one] at h'
  have key := congrArg (gm r z (LB.wchart L (fun _ => φ) (fun _ => p) ⊓ LB.wchart L' (fun _ => φ) (fun _ => q))) h'
  rw [map_mul, gm_res r z (U := LB.wchart L (fun _ => φ) (fun _ => p)) _ hV (b.s (fun _ => p))] at key
  refine key.trans (congrArg₂ (· * ·) ((gm_res r z _ hV _).trans
    (gm_pullU_eq_gm_comp φ r z (U := L.U p ⊓ L'.U q) ⟨hp, hq⟩ (w.s (p, q)))) (gm_res r z _ hV _))
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
