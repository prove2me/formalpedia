-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_unitPoint_generates_6a659f9ce924
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:11:38.730066+00:00
-- url     : https://prove2.me/submissions/618888f2-5c40-4171-9952-8b2fb04a0fbf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_TargetSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable (n)
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution :
    (∀ j : Fin (0 + 1), (fun _ ↦ (1 : ℚ)) j ∈ Geo.chartLat (ι := blockIdx fun _ : Unit ↦ 0) unitPoint 0 1) ∧
      ArakelovGeometry.KH.GeneratesOn (ι := blockIdx fun _ : Unit ↦ 0) unitPoint 0 (fun _ : Fin (0 + 1) ↦ (1 : ℚ)) := by
  refine ⟨fun j c _ ↦ by simp [one_mem], fun c _ ↦ ⟨fun _ ↦ 1, fun _ ↦ one_mem _, by simp⟩⟩
end GroundTheory.Heights₂.Heights
