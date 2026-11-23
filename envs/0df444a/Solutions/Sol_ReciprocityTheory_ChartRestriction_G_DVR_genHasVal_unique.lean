-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.genHasVal_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:38.649298+00:00
-- url     : https://prove2.me/submissions/a220616d-879b-45e0-b4c6-e8ac76810e87

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_exists_chart_top
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_genHasVal_top
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_hasVal_mul_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_hasVal_unique


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
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (hϖ : Irreducible ϖ) {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) {Ix : Type} [Fintype Ix]
    (φ : Ix → (Spec (CommRingCat.of V) ⟶ X)) (φ' : Ix → (Spec (CommRingCat.of (FractionRing V)) ⟶ X))
    (hφ : ∀ k, φ' k = jK V ≫ φ k) (ε : Ix → ℤ) (t : LB.Gen (LB.LinComb L φ' ε)) {n m : ℤ}
    (hn : GenHasVal ϖ L φ φ' hφ ε t n) (hm : GenHasVal ϖ L φ φ' hφ ε t m) : n = m := by
  obtain rfl : φ' = fun k => jK V ≫ φ k := funext hφ
  obtain ⟨j₀, htop⟩ := exists_chart_top L hL φ ε
  have hK : (⊤ : (Spec (CommRingCat.of (FractionRing V))).Opens) ≤
      LB.wchart L (fun k => jK V ≫ φ k) j₀ := by
    intro y _
    have hy : (jK V).base y ∈ LB.wchart L φ j₀ := by
      rw [htop]
      trivial
    have hy' : (jK V).base y ∈ (⋂ k, (φ k).base ⁻¹' (L.U (j₀ k) : Set X)) := hy
    show y ∈ (⋂ k, (jK V ≫ φ k).base ⁻¹' (L.U (j₀ k) : Set X))
    refine Set.mem_iInter.2 fun k => ?_
    have h1 := Set.mem_iInter.1 hy' k
    simpa using h1
  obtain ⟨c1, hc1, u1, h1⟩ := genHasVal_top L φ ε t hn j₀ htop hK
  obtain ⟨c2, hc2, u2, h2⟩ := genHasVal_top L φ ε t hm j₀ htop hK
  have h12 : c1 * algebraMap V (FractionRing V) (u1 : V) = c2 * algebraMap V (FractionRing V) (u2 : V) :=
    h1.symm.trans h2
  refine hasVal_unique hϖ (hasVal_mul_unit hc1 u1) ?_
  rw [h12]
  exact hasVal_mul_unit hc2 u2
end ReciprocityTheory.ChartRestriction.G.DVR
