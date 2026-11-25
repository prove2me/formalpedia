-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.inverse_generator_isGenerator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:48:18.127211+00:00
-- url     : https://prove2.me/submissions/cbe5c554-eed3-4ef7-926a-4b74c95fd769

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull

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
open ReciprocityTheory.ChartRestriction.G.Semi
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (i j : K → L.ι) :
    res (inf_le_left : (LB.LinComb L φ (fun k => -ε k)).U i ⊓ (LB.LinComb L φ (fun k => -ε k)).U j ≤
        (LB.LinComb L φ (fun k => -ε k)).U i) ((LB.invGen L φ ε t).s i) =
      (LB.LinComb L φ (fun k => -ε k)).g i j *
        res (inf_le_right : (LB.LinComb L φ (fun k => -ε k)).U i ⊓ (LB.LinComb L φ (fun k => -ε k)).U j ≤
          (LB.LinComb L φ (fun k => -ε k)).U j) ((LB.invGen L φ ε t).s j) := by
  have h1 := ht i j
  have hg : (LB.LinComb L φ (fun k => -ε k)).g i j = ((LB.LinComb L φ ε).g i j)⁻¹ := by
    (simp only [LB.LinComb, zpow_neg, Finset.prod_inv_distrib]) <;> rfl
  have h2 := congrArg (fun z => z⁻¹) h1
  simp only [mul_inv, ← map_inv] at h2
  rw [hg]
  exact h2
end ReciprocityTheory.ChartRestriction.G.DVR
