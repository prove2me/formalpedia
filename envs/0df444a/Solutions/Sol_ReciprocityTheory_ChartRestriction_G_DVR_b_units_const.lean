-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.b_units_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:52:04.95868+00:00
-- url     : https://prove2.me/submissions/11c7d1a5-c8a0-465b-81c1-f812560b6a51

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RValue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExpandsAtScale

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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (hGF : GlobalFnsSt) (D : DegData V (maximalIdeal V)) (f : Γ(D.toPre.P.A.left, ⊤)ˣ) :
    ∃ c : Γ(Spec (CommRingCat.of V), ⊤)ˣ, f = Units.map (D.toPre.P.A.hom.appTop).hom.toMonoidHom c := by
  have hbij := @hGF _ D.toPre.P.A D.toPre.P.grp D.toPre.P.isAb
  obtain ⟨c0, hc0⟩ := hbij.2 (f : Γ(D.toPre.P.A.left, ⊤))
  obtain ⟨c1, hc1⟩ := hbij.2 ((f⁻¹ : Γ(D.toPre.P.A.left, ⊤)ˣ) : Γ(D.toPre.P.A.left, ⊤))
  have h01 : c0 * c1 = 1 := hbij.1 (by rw [map_mul, hc0, hc1, Units.mul_inv, map_one])
  refine ⟨⟨c0, c1, h01, by rw [mul_comm]; exact h01⟩, ?_⟩
  ext
  exact hc0.symm
end ReciprocityTheory.ChartRestriction.G.DVR
