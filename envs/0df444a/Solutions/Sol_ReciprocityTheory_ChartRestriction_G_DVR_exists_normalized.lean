-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.exists_normalized
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:31:59.829341+00:00
-- url     : https://prove2.me/submissions/b2b82dfd-e169-4072-aa99-db1dbc2fe4dd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_scaleGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_exists_value
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pull_pull_id
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_res_res__b0a8af1c3378


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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε))
    (ht : t.IsGen) (p : Y ⟶ Z) (z : Z ⟶ Y) (hzp : z ≫ p = 𝟙 Z) (h0 : fsum (fun k => z ≫ φ k) ε = 0) :
    ∃ t' : LB.Gen (LB.LinComb L φ ε), t'.IsGen ∧
      ∀ j : K → L.ι, LB.Coh L (fun k => z ≫ φ k) j → (LB.pullGen L φ ε t' z).s j = 1 := by
  obtain ⟨c, hc⟩ := exists_value hL φ ε t ht z h0
  let c' : Γ(Y, ⊤)ˣ := res (fun _ _ => trivial : (⊤ : Y.Opens) ≤ p ⁻¹ᵁ ⊤) (pullU p ⊤ c⁻¹)
  refine ⟨scaleGen c' t, scaleGen_isGen c' t ht, fun j hj => ?_⟩
  have e := hc j hj
  show res _ (pullU z _ (res le_top c' * t.s j)) = 1
  rw [map_mul, map_mul]
  have e1 : res (wchart_comp_le φ z j) (pullU z _ (res (le_top : (LB.LinComb L φ ε).U j ≤ ⊤) c')) =
      res (le_top : LB.wchart L (fun k => z ≫ φ k) j ≤ ⊤) c⁻¹ := by
    simp only [c']
    erw [res_res']
    exact pull_pull_id z p hzp _ _ c⁻¹
  erw [e1]
  have e2 : res (wchart_comp_le φ z j) (pullU z _ (t.s j)) = (LB.pullGen L φ ε t z).s j := rfl
  erw [e2, ← e, ← map_mul, inv_mul_cancel, map_one]
  rfl
end ReciprocityTheory.ChartRestriction.G.DVR
