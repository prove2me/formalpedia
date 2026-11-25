-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualLineSemipositiveAlt_dualLine_h_eq_61af8b077351
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:37:57.573695+00:00
-- url     : https://prove2.me/submissions/53a3099e-b88e-4de1-9a43-7369cf70504c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualLineSemipositive
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualLineSemipositiveAlt_re_star_dotProduct_mulVec_1cf65725569f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualLineSemipositiveAlt_factor_spec_a65f990758a3
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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix NumberField
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.DualLineSemipositiveAlt
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]
omit [Fintype T] [DecidableEq T]
namespace GroundTheory.Heights₂.Heights.DualLineSemipositiveAlt
theorem _root_.solution {F : HermLattice K i} (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : (Σ _ : Unit, T) → ℂ) :
    (dualLine F b hb).h z = (fsMetric ((K →+* ℂ) × Fin i)).ρ (coordMap b hb z) := by
  show Real.sqrt (dualNormSq b hb fun t => z ⟨(), t⟩) = ‖WithLp.toLp 2 (coordMap b hb z)‖
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp only [dualNormSq]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [factor_spec F σ, re_star_dotProduct_mulVec]
  rfl
end GroundTheory.Heights₂.Heights.DualLineSemipositiveAlt
