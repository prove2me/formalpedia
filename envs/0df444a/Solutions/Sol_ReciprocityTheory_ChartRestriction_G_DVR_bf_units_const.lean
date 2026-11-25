-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.bf_units_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:09:49.93442+00:00
-- url     : https://prove2.me/submissions/491b5b4c-9bce-4581-8bf2-89e1d2234e4e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullGen

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (hGF : GlobalFnsSt) (hBC : PolBaseChangeSt) (f : Γ((DegPre.BF D.toPre F).left, ⊤)ˣ) :
    ∃ c : Γ((TF (R := V) F).left, ⊤)ˣ,
      f = Units.map ((fst (TF (R := V) F) D.toPre.P.A).left.appTop).hom.toMonoidHom c := by
  obtain ⟨P', g, hg, -, -, -⟩ := hBC _ _ (TF (R := V) F).hom D.toPre.P
  have hbij := @hGF _ P'.A P'.grp P'.isAb
  let e : P'.A.left ≅ pullback (TF (R := V) F).hom D.toPre.P.A.hom := hg.flip.isoPullback
  have he : e.hom ≫ pullback.fst _ _ = P'.A.hom := hg.flip.isoPullback_hom_fst
  let φ : P'.A.left ⟶ (DegPre.BF D.toPre F).left := e.hom
  have hφinj : Function.Injective φ.appTop.hom := by
    have key : ∀ x, e.inv.appTop.hom (φ.appTop.hom x) = x := by
      intro x
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, e.inv_hom_id, Scheme.Hom.id_appTop]
      rfl
    intro x y hxy
    rw [← key x, ← key y, hxy]
  have hcomp : ∀ c : Γ((TF (R := V) F).left, ⊤),
      φ.appTop.hom ((fst (TF (R := V) F) D.toPre.P.A).left.appTop.hom c) = P'.A.hom.appTop.hom c := by
    intro c
    rw [← he]
    rw [Scheme.Hom.comp_appTop]
    rfl
  obtain ⟨c0, hc0⟩ := hbij.2 (φ.appTop.hom (f : Γ((DegPre.BF D.toPre F).left, ⊤)))
  obtain ⟨c1, hc1⟩ := hbij.2 (φ.appTop.hom ((f⁻¹ : Γ((DegPre.BF D.toPre F).left, ⊤)ˣ) : Γ((DegPre.BF D.toPre F).left, ⊤)))
  have h01 : c0 * c1 = 1 := hbij.1 (by rw [map_mul, hc0, hc1, ← map_mul, Units.mul_inv, map_one, map_one])
  refine ⟨⟨c0, c1, h01, by rw [mul_comm]; exact h01⟩, ?_⟩
  ext
  apply hφinj
  show φ.appTop.hom (f : Γ((DegPre.BF D.toPre F).left, ⊤)) =
    φ.appTop.hom ((fst (TF (R := V) F) D.toPre.P.A).left.appTop.hom c0)
  rw [hcomp, hc0]
end ReciprocityTheory.ChartRestriction.G.DVR
