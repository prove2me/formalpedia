-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_of_gm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:03:41.948624+00:00
-- url     : https://prove2.me/submissions/bd8e4550-66a9-4c31-8863-c0378981bb60

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
section Transport
variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
private theorem gm_res_pullU_lemma_2 {A B C : Scheme.{0}} (f : B ⟶ A) (U : A.Opens) (V : B.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (r : C ⟶ B) (c : C) (hc : r c ∈ V) (s : Γ(A, U)ˣ) :
    gm r c V (res h (pullU f U s)) = gm (r ≫ f) c U s := by
  have hc' : (r ≫ f) c ∈ U := by simpa using h hc
  unfold gm
  rw [dif_pos hc, dif_pos hc']
  have hc2 : c ∈ r ⁻¹ᵁ V := hc
  have hc3 : c ∈ r ⁻¹ᵁ f ⁻¹ᵁ U := hc'
  have key : f.app U ≫ B.presheaf.map (homOfLE h).op ≫ r.app V ≫ C.presheaf.germ (r ⁻¹ᵁ V) c hc2 =
      f.app U ≫ r.app (f ⁻¹ᵁ U) ≫ C.presheaf.germ (r ⁻¹ᵁ f ⁻¹ᵁ U) c hc3 := by
    rw [Scheme.Hom.naturality_assoc, TopCat.Presheaf.germ_res]
  ext
  exact congrArg (fun φ => CommRingCat.Hom.hom φ (s : Γ(A, U))) key
private theorem units_ext_gm_lemma_3 {A : Scheme.{0}} {V : A.Opens} (a b : Γ(A, V)ˣ)
    (H : ∀ (y : A) (hy : y ∈ V), gm (𝟙 A) y V a = gm (𝟙 A) y V b) : a = b := by
  have key : ∀ (y : A) (hy : y ∈ V) (s : Γ(A, V)ˣ),
      ((gm (𝟙 A) y V s : A.presheaf.stalk y)) = A.presheaf.germ V y hy (s : Γ(A, V)) := by
    intro y hy s
    have hy1 : (𝟙 A) y ∈ V := by simpa using hy
    simp only [gm, dif_pos hy1]
    first
    | rfl
    | simp [pullU]
  ext
  refine TopCat.Presheaf.section_ext A.sheaf V _ _ fun y hy => ?_
  have h := congrArg Units.val (H y hy)
  rw [key y hy, key y hy] at h
  exact h
private theorem gm_res_lemma_4 {B C : Scheme.{0}} {U V : B.Opens} (h : V ≤ U) (r : C ⟶ B) (c : C)
    (hc : r c ∈ V) (s : Γ(B, U)ˣ) : gm r c V (res h s) = gm r c U s := by
  have hc' : r c ∈ U := h hc
  unfold gm
  rw [dif_pos hc, dif_pos hc']
  have hc2 : c ∈ r ⁻¹ᵁ V := hc
  have hc3 : c ∈ r ⁻¹ᵁ U := hc'
  have key : B.presheaf.map (homOfLE h).op ≫ r.app V ≫ C.presheaf.germ (r ⁻¹ᵁ V) c hc2 =
      r.app U ≫ C.presheaf.germ (r ⁻¹ᵁ U) c hc3 := by
    rw [Scheme.Hom.naturality_assoc, TopCat.Presheaf.germ_res]
  ext
  exact congrArg (fun φ => CommRingCat.Hom.hom φ (s : Γ(B, U))) key
end Transport
section Pull
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'}
end Pull
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {M : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb M φ ε))
    (h : ∀ (y : Y) (j j' : K → M.ι), y ∈ LB.wchart M φ j → y ∈ LB.wchart M φ j' →
      gm (𝟙 Y) y (LB.wchart M φ j) (t.s j) = trF φ ε (𝟙 Y) y j j' * gm (𝟙 Y) y (LB.wchart M φ j') (t.s j')) : t.IsGen := by
  intro i j
  apply units_ext_gm_lemma_3
  intro y hy
  have hi : y ∈ LB.wchart M φ i := hy.1
  have hj : y ∈ LB.wchart M φ j := hy.2
  have hk : ∀ k, LB.wchart M φ i ⊓ LB.wchart M φ j ≤ φ k ⁻¹ᵁ (M.U (i k) ⊓ M.U (j k)) :=
    fun k => le_inf (inf_le_left.trans (LB.wchart_le M φ i k)) (inf_le_right.trans (LB.wchart_le M φ j k))
  have eg : gm (𝟙 Y) y (LB.wchart M φ i ⊓ LB.wchart M φ j)
      (∏ k, res (hk k) (pullU (φ k) (M.U (i k) ⊓ M.U (j k)) (M.g (i k) (j k))) ^ ε k) =
        trF φ ε (𝟙 Y) y i j := by
    simp only [trF, map_prod, map_zpow]
    refine Finset.prod_congr rfl fun k _ => ?_
    exact congrArg (· ^ ε k) (gm_res_pullU_lemma_2 (φ k) _ _ (hk k) (𝟙 Y) y hy _)
  have e1 : gm (𝟙 Y) y (LB.wchart M φ i ⊓ LB.wchart M φ j) (res inf_le_left (t.s i)) =
      gm (𝟙 Y) y (LB.wchart M φ i) (t.s i) := gm_res_lemma_4 inf_le_left (𝟙 Y) y hy (t.s i)
  have e2 : gm (𝟙 Y) y (LB.wchart M φ i ⊓ LB.wchart M φ j) (res inf_le_right (t.s j)) =
      gm (𝟙 Y) y (LB.wchart M φ j) (t.s j) := gm_res_lemma_4 inf_le_right (𝟙 Y) y hy (t.s j)
  rw [map_mul]
  exact e1.trans ((h y i j hi hj).trans (congrArg₂ (· * ·) eg.symm e2.symm))
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
