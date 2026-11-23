-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.trF_trans
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:57.462696+00:00
-- url     : https://prove2.me/submissions/a9ca3f12-c918-48a2-a01b-a4e62fcd4360

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


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
theorem _root_.solution (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) {i j k : K → L.ι}
    (hi : r z ∈ LB.wchart L φ i) (hj : r z ∈ LB.wchart L φ j) (hk : r z ∈ LB.wchart L φ k) :
    trF φ ε r z i j * trF φ ε r z j k = trF φ ε r z i k := by
  unfold trF
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [← mul_zpow]
  congr 1
  have hm : (r ≫ φ c) z ∈ L.U (i c) ⊓ L.U (j c) ⊓ L.U (k c) :=
    ⟨⟨Set.mem_iInter.1 hi c, Set.mem_iInter.1 hj c⟩, Set.mem_iInter.1 hk c⟩
  have c1 := congrArg (gm (r ≫ φ c) z (L.U (i c) ⊓ L.U (j c) ⊓ L.U (k c))) (hL.cocycle (i c) (j c) (k c))
  rw [map_mul] at c1
  exact (congrArg₂ (· * ·) (gm_res (r ≫ φ c) z _ hm _) (gm_res (r ≫ φ c) z _ hm _)).symm.trans
    (c1.trans (gm_res (r ≫ φ c) z _ hm _))
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
