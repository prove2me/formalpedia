-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_ValPt___ab_adaeffd89a42
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:25:45.26101+00:00
-- url     : https://prove2.me/submissions/77fcf4ab-3f5c-4547-b02a-7de8e783e1ee

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrData
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [instance] UnramExt.ring UnramExt.dom UnramExt.dvr UnramExt.alg
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
private theorem comp_apply_point {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (x : A) :
    (f ≫ g) x = g (f x) := rfl
private theorem spMap_comp_xi_eq_spMap_lift_comp_y_comp_j (P : ValPt Y) (W : UnramExt P.V) (lift : P.K' →+* FractionRing W.W)
    (hlift : lift.comp (algebraMap P.V P.K') =
      (algebraMap W.W (FractionRing W.W)).comp (algebraMap P.V W.W)) :
    spMap (algebraMap W.W (FractionRing W.W)) ≫ P.ξ W = spMap lift ≫ P.y ≫ Y.j := by
  rw [← P.ext]
  simp only [ValPt.ξ, spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hlift]
private theorem sp_nonempty_of_field (R : Type) [Field R] : Nonempty (Sp R) :=
  ⟨(⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum R)⟩
private theorem jQ_mem_preimage_abLocus (p : Xo.XF c) :
    Y.jQ p ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
  rw [Y.ab_gen]
  exact Set.mem_range_self _
private theorem exists_lift_fractionRing_comp_algebraMap (P : ValPt Y) (W : UnramExt P.V) :
    ∃ f : P.K' →+* FractionRing W.W, f.comp (algebraMap P.V P.K') =
      (algebraMap W.W (FractionRing W.W)).comp (algebraMap P.V W.W) := by
  haveI := P.frac
  have hinj : Function.Injective
      ((algebraMap W.W (FractionRing W.W)).comp (algebraMap P.V W.W)) := by
    rw [RingHom.coe_comp]
    exact (IsFractionRing.injective W.W (FractionRing W.W)).comp W.inj
  refine ⟨IsFractionRing.lift hinj, RingHom.ext fun x => ?_⟩
  simp only [RingHom.comp_apply, IsFractionRing.lift_algebraMap]
private theorem xi_spMap_eq_pullback_fst_jQ (P : ValPt Y) (W : UnramExt P.V) (lift : P.K' →+* FractionRing W.W)
    (hlift : lift.comp (algebraMap P.V P.K') =
      (algebraMap W.W (FractionRing W.W)).comp (algebraMap P.V W.W))
    (z : Sp (FractionRing W.W)) :
    (P.ξ W) (spMap (algebraMap W.W (FractionRing W.W)) z) =
      pullback.fst Y.s (spMap β) (Y.jQ (P.y (spMap lift z))) := by
  rw [← comp_apply_point, spMap_comp_xi_eq_spMap_lift_comp_y_comp_j P W lift hlift, comp_apply_point, comp_apply_point, Model.j, comp_apply_point]
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [instance] UnramExt.ring UnramExt.dom UnramExt.dvr UnramExt.alg
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace ValPt
theorem _root_.solution (P : ValPt Y) (W : UnramExt P.V) : (P.ξ W ⁻¹' abLocus Y.t.G).Nonempty := by
  obtain ⟨lift, hlift⟩ := exists_lift_fractionRing_comp_algebraMap P W
  obtain ⟨z⟩ := sp_nonempty_of_field (FractionRing W.W)
  refine ⟨spMap (algebraMap W.W (FractionRing W.W)) z, ?_⟩
  rw [Set.mem_preimage, xi_spMap_eq_pullback_fst_jQ P W lift hlift z]
  exact Set.mem_preimage.mp (jQ_mem_preimage_abLocus (Y := Y) _)
end ValPt
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
