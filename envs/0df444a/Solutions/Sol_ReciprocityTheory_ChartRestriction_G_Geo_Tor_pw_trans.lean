-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.pw_trans
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:19.719918+00:00
-- url     : https://prove2.me/submissions/370136d8-dda0-45e0-a281-aa18506163be

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
theorem _root_.solution {w : LB.Iso L' (L.pull F)} (hw : PGen w) (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z)
    {p p' : K → L.ι} {q q' : K → L'.ι} (hp : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p)
    (hp' : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p') (hq : r z ∈ LB.wchart L' φ' q) (hq' : r z ∈ LB.wchart L' φ' q') :
    pw w φ' ε r z p q = trF (fun k => φ' k ≫ F) ε r z p p' * (trF φ' ε r z q q')⁻¹ * pw w φ' ε r z p' q' := by
  rw [mem_wchart_lemma] at hp hp' hq hq'
  simp only [pw, trF]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [hw Z (r ≫ φ' k) z (p k) (p' k) (q k) (q' k) (by simpa using hp k) (by simpa using hp' k)
    (by simpa using hq k) (by simpa using hq' k)]
  simp only [Category.assoc, mul_zpow, inv_zpow]
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
