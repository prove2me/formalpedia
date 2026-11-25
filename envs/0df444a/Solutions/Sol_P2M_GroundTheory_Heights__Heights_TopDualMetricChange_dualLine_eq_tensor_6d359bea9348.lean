-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TopDualMetricChange_dualLine_eq_tensor_6d359bea9348
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:51:41.182667+00:00
-- url     : https://prove2.me/submissions/9f7af710-cb7f-46ea-9fc9-0f626755a103

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ScaledExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsDualEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualLineSemipositive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PIntDomainDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ReMulOfPos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualTopMetricChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TopDualMetricChange_hermLine_ext_becd6d44a974
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TopDualMetricChange_dualLine_h_zero_4d8dfe6e25aa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.TopDualMetricChange
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]
namespace GroundTheory.Heights₂.Heights.TopDualMetricChange
theorem _root_.solution (F : HermLattice K i) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) :
    dualLine F b hb = (dualLine F.withStdMetric b hb).tensor
      (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight (weight F b hb) (weight_hom F b hb)) := by
  refine hermLine_ext (funext fun _ => by simp [ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight, dualLine]) ?_
  funext z
  show (dualLine F b hb).h z = (dualLine F.withStdMetric b hb).h z * Real.exp (-weight F b hb z)
  by_cases hz : ∀ k : Unit, ∃ t, z ⟨k, t⟩ ≠ 0
  · have h1 := (dualLine F.withStdMetric b hb).pos z hz
    have h2 := (dualLine F b hb).pos z hz
    rw [weight, neg_sub, Real.exp_sub, Real.exp_log h1, Real.exp_log h2]
    field_simp
  · rw [dualLine_h_zero F b hb z hz, dualLine_h_zero F.withStdMetric b hb z hz, zero_mul]
end GroundTheory.Heights₂.Heights.TopDualMetricChange
