-- Prove2me | solution 1 for PI.KFinSmoothW.Gard.contDiff_mat_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:15.224345+00:00
-- url     : https://prove2.me/submissions/6b1883b9-b441-46f1-abae-33a1ff58ab35

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_UnitaryModelOfMultiplicityGardingDensity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_Garding
import Theorems.Thm_PI_KFinSmoothW_Gard_contDiff_mat_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology Set Metric
open scoped InnerProductSpace ContDiff
noncomputable section
open PI PI.KFinSmoothW
open PI.UpqRep
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PI.KFinSmoothW.Gard
attribute [local instance] mMeas
attribute [local instance] mBorel
attribute [local instance] mBorelN
attribute [local instance] mLocCpt
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} {N : WithTop ℕ∞}
namespace PI.KFinSmoothW.Gard
theorem _root_.solution {f g : E → Matrix (Fin n) (Fin n) ℂ} (hf : ContDiff ℝ N f)
    (hg : ContDiff ℝ N g) : ContDiff ℝ N (fun x => f x * g x) := by
  rw [contDiff_mat_iff] at hf hg ⊢
  intro i j
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun k _ => (hf i k).mul (hg k j)
end PI.KFinSmoothW.Gard
