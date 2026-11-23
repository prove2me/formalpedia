-- Prove2me | solution 1 for P2M_GlobalTheory_ComplexPoints_isUnit_of_valAt__ne_zero_23aaec802820
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:20:49.097355+00:00
-- url     : https://prove2.me/submissions/03c24104-7ae2-4ba2-8c3f-369db8ea9eff

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Theorems.Thm_GlobalTheory_ComplexPoints_exists_point_mem
import Theorems.Thm_GlobalTheory_ComplexPoints_top_le_preimage_iff
import Theorems.Thm_GlobalTheory_ComplexPoints_top_le_preimage_basicOpen_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
universe u
namespace GlobalTheory.ComplexPoints
section General
variable {K : Type u} [Field K] [IsAlgClosed K]
end General
variable {X Y : Scheme.{0}}
set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {X Y : Scheme.{0}} in
private theorem opens_le_of_forall_complex_section (p : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) [LocallyOfFiniteType p]
    (U V : X.Opens)
    (h : ∀ x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → ⊤ ≤ x ⁻¹ᵁ V) : U ≤ V := by
  intro y hyU
  by_contra hyV
  obtain ⟨x, hx1, hx2⟩ := _root_.GlobalTheory.ComplexPoints.exists_point_mem (K := ℂ) p
    (Z := (U : Set X) ∩ (V : Set X)ᶜ)
    (U.isOpen.isLocallyClosed.inter V.isOpen.isClosed_compl.isLocallyClosed) ⟨y, hyU, hyV⟩
  obtain ⟨a⟩ := (inferInstance : Nonempty (Spec (.of ℂ)))
  have hU : ⊤ ≤ x ⁻¹ᵁ U := (_root_.GlobalTheory.ComplexPoints.top_le_preimage_iff x U a).mpr (hx2 a).1
  exact (hx2 a).2 ((_root_.GlobalTheory.ComplexPoints.top_le_preimage_iff x V a).mp (h x hx1 hU))
end GlobalTheory.ComplexPoints
namespace GlobalTheory
end GlobalTheory
end

set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
universe u
open GlobalTheory GlobalTheory.ComplexPoints
variable {X Y : Scheme.{0}}
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
variable {X Y : Scheme.{0}}
namespace GlobalTheory.ComplexPoints
namespace _root_.GlobalTheory.ComplexPoints
theorem _root_.solution (p : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) [LocallyOfFiniteType p]
    (U : X.Opens) (f : Γ(X, U))
    (h : ∀ x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' x U f ≠ 0) : IsUnit f := by
  have hle : U ≤ X.basicOpen f := opens_le_of_forall_complex_section p U _ fun x hx hU => by
    have := h x hx hU
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' at this
    rw [dif_pos hU] at this
    exact (_root_.GlobalTheory.ComplexPoints.top_le_preimage_basicOpen_iff x U hU f).mpr this
  have hu := (X.toRingedSpace.isUnit_res_basicOpen f).map
    (X.presheaf.map (homOfLE hle).op).hom
  have hid : (homOfLE (X.basicOpen_le f)).op ≫ (homOfLE hle).op = 𝟙 (Opposite.op U) :=
    Subsingleton.elim _ _
  convert hu using 1
  erw [← CommRingCat.comp_apply, ← Functor.map_comp, hid, CategoryTheory.Functor.map_id,
    CommRingCat.id_apply]
end _root_.GlobalTheory.ComplexPoints
end GlobalTheory.ComplexPoints
