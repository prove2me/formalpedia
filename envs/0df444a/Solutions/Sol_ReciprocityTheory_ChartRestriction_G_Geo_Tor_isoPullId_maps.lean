-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.isoPullId_maps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:29:01.852007+00:00
-- url     : https://prove2.me/submissions/027ec2ba-2636-43a6-bc3f-3ac9a7f33352

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AdmissibleBasePowerSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleIdentityIso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gw_isoPullId
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_maps_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
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
private theorem res_eq_mul_res_of_gm_id_eq_mul {Y : Scheme.{0}} {V U₁ U₃ : Y.Opens} {h₁ : V ≤ U₁} {h₃ : V ≤ U₃}
    {a : Γ(Y, U₁)ˣ} {m : Γ(Y, V)ˣ} {c : Γ(Y, U₃)ˣ}
    (H : ∀ y ∈ V, gm (𝟙 Y) y U₁ a = gm (𝟙 Y) y V m * gm (𝟙 Y) y U₃ c) :
    res h₁ a = m * res h₃ c := by
  apply Units.ext
  refine TopCat.Presheaf.section_ext Y.sheaf V _ _ (fun y hy => ?_)
  have key := H y hy
  rw [← gm_res (𝟙 Y) y h₁ hy a, ← gm_res (𝟙 Y) y h₃ hy c, ← map_mul] at key
  have hy' : (𝟙 Y) y ∈ V := hy
  simp only [gm, dif_pos hy', MonoidHom.comp_apply] at key
  have key2 := congrArg Units.val key
  exact key2
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
theorem _root_.solution {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L' L : RigLB G} {w : LB.Iso L'.L L.L}
    (hm : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L'.rig L.rig)
    {F : G.left ⟶ G.left} (hF : F = 𝟙 _) {e : (𝟙_ (Over S)).left ⟶ (𝟙_ (Over S)).left} (he₀ : e = 𝟙 _)
    (he : eSec G ≫ F = e ≫ eSec G) :
    LB.Gen.Maps (LB.linCombIso (isoPullId w hF) (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L'.rig
      (rigPullOf F e he L.L L.rig) := by
  subst hF he₀
  rintro ⟨j, i⟩
  have hmid : (LB.linCombIso (isoPullId w (rfl : 𝟙 G.left = 𝟙 G.left)) (K := PUnit) (fun _ => eSec G)
      (fun _ => 1)).s (j, i) =
      res (U := eSec G ⁻¹ᵁ ((L.L.pull (𝟙 G.left)).U (j PUnit.unit) ⊓ L'.L.U (i PUnit.unit)))
        (V := LB.wchart (L.L.pull (𝟙 G.left)) (fun _ => eSec G) j ⊓ LB.wchart L'.L (fun _ => eSec G) i)
        (le_inf (inf_le_left.trans (LB.wchart_le (L.L.pull (𝟙 G.left)) (fun _ => eSec G) j PUnit.unit))
          (inf_le_right.trans (LB.wchart_le L'.L (fun _ => eSec G) i PUnit.unit)))
        (pullU (eSec G) ((L.L.pull (𝟙 G.left)).U (j PUnit.unit) ⊓ L'.L.U (i PUnit.unit))
          ((isoPullId w (rfl : 𝟙 G.left = 𝟙 G.left)).s (j PUnit.unit, i PUnit.unit))) :=
    by
      simp only [LB.linCombIso, zpow_one]
      first
        | exact Fintype.prod_unique _
        | exact Fintype.prod_unique
        | simp
  refine res_eq_mul_res_of_gm_id_eq_mul (fun z hz => ?_)
  have hz1' := mem_pull.1 (mem_pull.1 hz.1)
  have hz2' := mem_pull.1 hz.2
  have hz1 : eSec G z ∈ L.L.U (j PUnit.unit PUnit.unit) := hz1'
  have hz2 : eSec G z ∈ L'.L.U (i PUnit.unit) := hz2'
  have eL := (gm_res (𝟙 _) z (rigPull_le (𝟙 G.left) (𝟙 _) he L.L j) hz.1
      (pullU (𝟙 _) _ (L.rig.s (fun _ => j PUnit.unit PUnit.unit)))).trans
    (gm_pullU_eq_gm_comp (𝟙 _) (𝟙 _) z (U := (L.L.pull (eSec G)).U (fun _ => j PUnit.unit PUnit.unit))
      (mem_pull.2 hz1) (L.rig.s (fun _ => j PUnit.unit PUnit.unit)))
  rw [Category.comp_id] at eL
  have eM := (congrArg (gm (𝟙 _) z _) hmid).trans ((gm_res (𝟙 _) z _ hz _).trans
    ((gm_pullU_eq_gm_comp (eSec G) (𝟙 _) z (U := (L.L.pull (𝟙 G.left)).U (j PUnit.unit) ⊓ L'.L.U (i PUnit.unit))
      ⟨mem_pull.2 hz1, hz2⟩ ((isoPullId w (rfl : 𝟙 G.left = 𝟙 G.left)).s (j PUnit.unit, i PUnit.unit))).trans
      (gw_isoPullId w rfl (𝟙 _ ≫ eSec G) z (j PUnit.unit PUnit.unit) (i PUnit.unit) hz1 hz2)))
  have eR := gm_maps_pt hm (𝟙 _) z (j PUnit.unit PUnit.unit) (i PUnit.unit) hz1 hz2
  exact eL.trans (eR.trans (congrArg (· * _) eM.symm))
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
