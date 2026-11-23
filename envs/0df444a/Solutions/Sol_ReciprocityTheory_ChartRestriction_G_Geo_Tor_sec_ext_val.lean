-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.sec_ext_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:19.154057+00:00
-- url     : https://prove2.me/submissions/911a5d5d-377b-47f0-b56b-c0979d8e56a4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_good

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
theorem _root_.solution (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {s s' : LB.Sec (LB.LinComb L φ ε)}
    (h : ∀ y J, Good L y J → sval s (𝟙 Y) y J = sval s' (𝟙 Y) y J) (j : K → L.ι) : s.f j = s'.f j := by
  apply fn_ext
  intro y hy
  obtain ⟨J, hJ, -⟩ := exists_good L hL y (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim (fun a => a.elim)
    (fun k => k.elim)
  exact (sec_trans s (𝟙 Y) y hy (hJ.mem φ (𝟙 Y))).trans
    ((congrArg ((trF φ ε (𝟙 Y) y j (fun k => J (𝟙 Y ≫ φ k))).val * ·) (h y J hJ)).trans
      (sec_trans s' (𝟙 Y) y hy (hJ.mem φ (𝟙 Y))).symm)
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
