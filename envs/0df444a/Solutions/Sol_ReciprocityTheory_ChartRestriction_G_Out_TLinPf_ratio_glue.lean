-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ratio_glue
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:57:49.303273+00:00
-- url     : https://prove2.me/submissions/94f02b61-cdb0-428b-b384-723fc1578919

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.TLinPf
open Semi
namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf
theorem _root_.solution {Y : Scheme.{0}} (L : LB Y) (hc : ⨆ j, L.U j = ⊤) (t t' : LB.Gen L)
    (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ ρ : Γ(Y, ⊤)ˣ, ∀ j, t.s j = res le_top ρ * t'.s j := by
  obtain ⟨s⟩ := t
  obtain ⟨s'⟩ := t'
  unfold LB.Gen.IsGen at ht ht'
  dsimp only at ht ht' ⊢
  have hcov : (⊤ : Y.Opens) ≤ ⨆ j, L.U j := hc.ge
  have key : ∀ (f : ∀ j, Γ(Y, L.U j)),
      (∀ i j, (Y.presheaf.map (homOfLE (inf_le_left : L.U i ⊓ L.U j ≤ L.U i)).op).hom (f i) =
        (Y.presheaf.map (homOfLE (inf_le_right : L.U i ⊓ L.U j ≤ L.U j)).op).hom (f j)) →
      ∃ r : Γ(Y, ⊤), ∀ j, (Y.presheaf.map (homOfLE (le_top : L.U j ≤ ⊤)).op).hom r = f j := by
    intro f hf
    obtain ⟨r, hr, -⟩ := TopCat.Sheaf.existsUnique_gluing' (F := Y.sheaf) (U := L.U) ⊤
      (fun j => homOfLE le_top) hcov f hf
    exact ⟨r, hr⟩
  have uniq : ∀ a b : Γ(Y, ⊤), (∀ j, (Y.presheaf.map (homOfLE (le_top : L.U j ≤ ⊤)).op).hom a =
      (Y.presheaf.map (homOfLE (le_top : L.U j ≤ ⊤)).op).hom b) → a = b := by
    intro a b h
    exact TopCat.Sheaf.eq_of_locally_eq' (F := Y.sheaf) (U := L.U) ⊤ (fun j => homOfLE le_top) hcov a b h
  have hu : ∀ i j, res (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (s i * (s' i)⁻¹) =
      res (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (s j * (s' j)⁻¹) := by
    intro i j
    rw [map_mul, map_inv, map_mul, map_inv, ht i j, ht' i j, _root_.mul_inv, _root_.mul_mul_mul_comm,
      _root_.mul_inv_cancel, _root_.one_mul]
  have hu' : ∀ i j, res (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (s i * (s' i)⁻¹)⁻¹ =
      res (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (s j * (s' j)⁻¹)⁻¹ := by
    intro i j
    rw [map_inv, map_inv, hu i j]
  obtain ⟨r, hr⟩ := key (fun j => ((s j * (s' j)⁻¹ : _ˣ) : Γ(Y, L.U j)))
    (fun i j => congrArg Units.val (hu i j))
  obtain ⟨r', hr'⟩ := key (fun j => (((s j * (s' j)⁻¹)⁻¹ : _ˣ) : Γ(Y, L.U j)))
    (fun i j => congrArg Units.val (hu' i j))
  have hrr : r * r' = 1 := by
    apply uniq
    intro j
    rw [map_mul, map_one, hr j, hr' j]
    exact Units.mul_inv _
  let ρ : Γ(Y, ⊤)ˣ := ⟨r, r', hrr, by rw [mul_comm]; exact hrr⟩
  refine ⟨ρ, fun j => ?_⟩
  have e : res (le_top : L.U j ≤ ⊤) ρ = s j * (s' j)⁻¹ := Units.ext (hr j)
  rw [e, inv_mul_cancel_right]
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
