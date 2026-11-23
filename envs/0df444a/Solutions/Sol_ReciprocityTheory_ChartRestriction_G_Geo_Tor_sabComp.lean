-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.sabComp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:18:31.137383+00:00
-- url     : https://prove2.me/submissions/4043ee3f-249e-4dcb-8722-ff3512ec3796

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArcSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (hC : PullCubCompSt) : SABCompSt := by
  intro E _ _ _ H S S' S'' t t' t'' f g m m'
  let cm : CubeMap t''.G t.G :=
    { F := m'.cm.F ≫ m.cm.F
      F3 := m'.cm.F3 ≫ m.cm.F3
      e := m'.cm.e ≫ m.cm.e
      e_comm := by
        rw [← Category.assoc, m'.cm.e_comm]
        simp only [Category.assoc, m.cm.e_comm]
      psum_comm := fun I => by
        rw [← Category.assoc, m'.cm.psum_comm I]
        simp only [Category.assoc, m.cm.psum_comm I] }
  refine ⟨{ cm := cm, cart := IsGrpPullback.comp m'.cart m.cart, base := ?_, act := ?_, lin := ?_ }, rfl⟩
  · show m'.cm.e ≫ m.cm.e = g ≫ f
    rw [m'.base, m.base]
  · intro a
    show _ ≫ (m'.cm.F ≫ m.cm.F) = (m'.cm.F ≫ m.cm.F) ≫ _
    rw [← Category.assoc, m'.act a]
    simp only [Category.assoc, m.act a]
  · exact hC S S' S'' t.G t'.G t''.G m.cm m'.cm cm t.PP t'.PP t''.PP t.cub t'.cub t''.cub rfl rfl rfl
      m.lin m'.lin
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
