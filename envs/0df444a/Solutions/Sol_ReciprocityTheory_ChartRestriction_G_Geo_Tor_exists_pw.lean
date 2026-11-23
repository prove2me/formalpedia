-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_pw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:20.176636+00:00
-- url     : https://prove2.me/submissions/b0a2ca4c-f07a-4176-8dc9-a5e19d873b0a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
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
private theorem mem_wchart_lemma {A B : Scheme.{0}} {Idx : Type} [Fintype Idx] (M : LB A) (ψ : Idx → (B ⟶ A))
    (j : Idx → M.ι) (b : B) : b ∈ LB.wchart M ψ j ↔ ∀ k, ψ k b ∈ M.U (j k) := by
  show b ∈ ⋂ k, (ψ k).base ⁻¹' (M.U (j k) : Set A) ↔ _
  exact Set.mem_iInter
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
theorem _root_.solution (w : LB.Iso L' (L.pull F)) (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (p : K → L.ι) (q : K → L'.ι) :
    ∃ u : Γ(Y, LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z),
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q → gm r z _ u = pw w φ' ε r z p q := by
  have hle : ∀ k, LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q ≤
      φ' k ⁻¹ᵁ ((L.pull F).U (fun _ => p k) ⊓ L'.U (q k)) := by
    intro k y hy
    have h1 := (mem_wchart_lemma _ _ _ _).mp hy.1
    have h2 := (mem_wchart_lemma _ _ _ _).mp hy.2
    show φ' k y ∈ ((L.pull F).U fun _ => p k) ⊓ L'.U (q k)
    exact ⟨(mem_wchart_lemma _ _ _ _).mpr fun _ => by simpa using h1 k, h2 k⟩
  refine ⟨∏ k, res (hle k) (pullU (φ' k) ((L.pull F).U (fun _ => p k) ⊓ L'.U (q k))
    (w.s (fun _ => p k, q k))) ^ ε k, ?_⟩
  intro Z r z hz
  simp only [pw, gw, map_prod, map_zpow]
  refine Finset.prod_congr rfl fun k _ => ?_
  exact congrArg (· ^ ε k) (gm_res_pullU_lemma_2 (φ' k) _ _ (hle k) r z hz _)
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
