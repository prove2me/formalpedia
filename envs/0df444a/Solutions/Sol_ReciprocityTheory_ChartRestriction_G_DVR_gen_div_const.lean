-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.gen_div_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:33:00.648206+00:00
-- url     : https://prove2.me/submissions/abeaffe3-71c6-4670-a112-4bbe884a32a9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_res_res__b0a8af1c3378

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
private lemma res_self_discrete_valuation_rings {Y : Scheme.{0}} {U : Y.Opens} (h : U ≤ U) (x : Γ(Y, U)ˣ) :
    res h x = x := by
  ext
  simp [res]
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
end ReciprocityTheory.ChartRestriction.G.DVR
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {Y : Scheme.{0}} {X : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (ψ : K → (Y ⟶ X))
    (ε : K → ℤ) (s s' : ∀ j : K → L.ι, Γ(Y, LB.wchart L ψ j)ˣ) (hs : IsGenW L ψ ε s) (hs' : IsGenW L ψ ε s')
    (j₀ : K → L.ι) (htop : LB.wchart L ψ j₀ = ⊤) (j : K → L.ι) :
    s j = res (by rw [htop]; exact le_top : LB.wchart L ψ j ≤ LB.wchart L ψ j₀) (s j₀ / s' j₀) * s' j := by
  have hfw : LB.wchart L ψ j ≤ LB.wchart L ψ j ⊓ LB.wchart L ψ j₀ :=
    le_inf le_rfl (by rw [htop]; exact le_top)
  have e1 := congrArg (res hfw) (hs j j₀)
  have e2 := congrArg (res hfw) (hs' j j₀)
  simp only [map_mul, res_res', res_self_discrete_valuation_rings] at e1 e2
  rw [map_div, e1, e2, mul_comm (res _ _) (res _ (s' j₀)), ← mul_assoc, div_mul_cancel, mul_comm]
end ReciprocityTheory.ChartRestriction.G.DVR
