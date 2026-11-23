-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.sval_trans
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:27.186633+00:00
-- url     : https://prove2.me/submissions/8e53f2ce-4d72-4245-8fd7-5bad183fb0f7

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
theorem _root_.solution (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (y : Y) (j : K → L.ι)
    (hy : y ∈ LB.wchart L φ j) : ∃ J, Good L y J ∧ gs (𝟙 Y) y (LB.wchart L φ j) (s.f j) =
      (trF φ ε (𝟙 Y) y j (fun k => J (𝟙 Y ≫ φ k))).val * sval s (𝟙 Y) y J := by
  obtain ⟨J, hJ, -⟩ := exists_good L hL y (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim (fun a => a.elim)
    (fun k => k.elim)
  exact ⟨J, hJ, sec_trans s (𝟙 Y) y hy (hJ.mem φ (𝟙 Y))⟩
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
