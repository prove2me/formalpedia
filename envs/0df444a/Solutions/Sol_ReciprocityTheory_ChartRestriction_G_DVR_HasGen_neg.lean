-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.HasGen.neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:46.965104+00:00
-- url     : https://prove2.me/submissions/eedb87c0-0d90-4904-b61b-1c4b7ac90f90

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen

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
variable {X Y Z : Scheme.{0}} (L : LB X)
variable {L}
namespace ReciprocityTheory.ChartRestriction.G.DVR
namespace HasGen
theorem _root_.solution {F : (Y ⟶ X) →₀ ℤ} (hF : HasGen L F) : HasGen L (-F) := by
  obtain ⟨K, _, φ, ε, rfl, g, hg⟩ := hF
  refine ⟨K, inferInstance, φ, fun k => -ε k, ?_, ⟨fun i => (g.s i)⁻¹⟩, ?_⟩
  · simp [fsum, Finsupp.single_neg, Finset.sum_neg_distrib]
  · intro i j
    have hgg : (LB.LinComb L φ (fun k => -ε k)).g i j = ((LB.LinComb L φ ε).g i j)⁻¹ := by
      first
        | (simp only [LB.LinComb, zpow_neg, Finset.prod_inv_distrib]; rfl)
        | (simp [LB.LinComb, zpow_neg, Finset.prod_inv_distrib]; rfl)
        | (unfold LB.LinComb; simp [zpow_neg, Finset.prod_inv_distrib])
    have hij := hg i j
    dsimp only
    rw [hgg]
    exact (MonoidHom.map_inv _ _).trans <| (congrArg (fun x => x⁻¹) hij).trans <|
      (mul_inv _ _).trans <|
        congrArg (fun y => ((LB.LinComb L φ ε).g i j)⁻¹ * y) (MonoidHom.map_inv _ _).symm
end HasGen
end ReciprocityTheory.ChartRestriction.G.DVR
