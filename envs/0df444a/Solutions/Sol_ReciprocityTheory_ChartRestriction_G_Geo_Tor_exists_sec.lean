-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_sec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:51:09.255553+00:00
-- url     : https://prove2.me/submissions/d2952da5-dc9a-4d92-a792-23fb2762874c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_trF_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


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
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Y' Z : Scheme.{0}}
variable (L : LB X)
variable {L} {K K' : Type} [Fintype K] [Fintype K']
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (h : FormEq φ ε φ' ε') (s : LB.Sec (LB.LinComb L φ ε)) : ∃ s' : LB.Sec (LB.LinComb L φ' ε'),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → sval s' r z J = sval s r z J := by
  have glue : ∀ j : K' → L.ι, ∃ a : Γ(Y, LB.wchart L φ' j), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (I : (Y ⟶ X) → L.ι),
      r z ∈ LB.wchart L φ' j → r z ∈ LB.wchart L φ' (fun k => I (φ' k)) → r z ∈ LB.wchart L φ (fun k => I (φ k)) →
      gs r z _ a = (trF φ' ε' r z j (fun k => I (φ' k))).val * gs r z (LB.wchart L φ (fun k => I (φ k))) (s.f (fun k => I (φ k))) := by
    intro j
    let W : ((Y ⟶ X) → L.ι) → Y.Opens := fun I =>
      LB.wchart L φ' j ⊓ LB.wchart L φ' (fun k => I (φ' k)) ⊓ LB.wchart L φ (fun k => I (φ k))
    obtain ⟨u, hu⟩ : ∃ u : ∀ I, Γ(Y, W I), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) I, r z ∈ W I →
        gs r z (W I) (u I) = (trF φ' ε' r z j (fun k => I (φ' k))).val * gs r z (LB.wchart L φ (fun k => I (φ k))) (s.f (fun k => I (φ k))) :=
      ⟨fun I => (Y.presheaf.map (homOfLE (inf_le_left : W I ≤ LB.wchart L φ' j ⊓ LB.wchart L φ' (fun k => I (φ' k)))).op).hom
          ((LB.LinComb L φ' ε').g j (fun k => I (φ' k))).val *
          (Y.presheaf.map (homOfLE (inf_le_right : W I ≤ LB.wchart L φ (fun k => I (φ k)))).op).hom (s.f (fun k => I (φ k))), fun Z r z I hz =>
        (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_res r z _ hz _).trans ((gs_unit r z _ hz.1 _).trans
          (congrArg Units.val (gm_linComb L φ' ε' r z _ _ hz.1.1 hz.1.2)))) (gs_res r z _ hz _))⟩
    obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' W (LB.wchart L φ' j)
      (fun I => homOfLE (inf_le_left.trans inf_le_left)) (fun y hy => by
        choose I hI using fun χ : Y ⟶ X => exists_chart hL (χ y)
        exact Opens.mem_iSup.2 ⟨I, ⟨hy, Set.mem_iInter.2 fun k => hI _⟩, Set.mem_iInter.2 fun k => hI _⟩) u
      (fun I I' => fn_ext (V := W I ⊓ W I') fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        rw [hu _ _ y I hy.1, hu _ _ y I' hy.2, sec_trans s (𝟙 Y) y hy.1.2 hy.2.2, h.trF, ← mul_assoc, ← Units.val_mul,
          trF_trans hL φ' ε' (𝟙 Y) y hy.1.1.1 hy.1.1.2 hy.2.1.2])
    refine ⟨a, fun Z r z I h₁ h₂ h₃ => ?_⟩
    have hz : r z ∈ W I := ⟨⟨h₁, h₂⟩, h₃⟩
    exact (gs_res r z (inf_le_left.trans inf_le_left) hz a).symm.trans ((congrArg (gs r z (W I)) (ha I)).trans
      (hu Z r z I hz))
  choose a ha using glue
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z J hJ => ?_⟩
  · choose I hI using fun χ : Y ⟶ X => exists_chart hL (χ y)
    have m₁ : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L φ' (fun k => I (φ' k)) := Set.mem_iInter.2 fun k => hI _
    have m₂ : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L φ (fun k => I (φ k)) := Set.mem_iInter.2 fun k => hI _
    refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L φ' ε' (𝟙 Y) y j j' hy.1 hy.2)))
      (gs_res (𝟙 Y) y _ hy _))).symm)
    refine (ha j _ (𝟙 Y) y I hy.1 m₁ m₂).trans (Eq.trans ?_ (congrArg _ (ha j' _ (𝟙 Y) y I hy.2 m₁ m₂)).symm)
    rw [← trF_trans hL φ' ε' (𝟙 Y) y hy.1 hy.2 m₁, Units.val_mul, mul_assoc]; rfl
  · have m := hJ.mem φ' r
    refine (ha _ Z r z (fun χ => J (r ≫ χ)) m m (hJ.mem φ r)).trans ?_
    rw [mul_eq_left.1 (trF_trans hL φ' ε' r z m m m), Units.val_one, one_mul]; rfl
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
