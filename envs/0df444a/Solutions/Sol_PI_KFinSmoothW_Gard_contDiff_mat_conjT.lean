-- Prove2me | solution 1 for PI.KFinSmoothW.Gard.contDiff_mat_conjT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:56:37.637829+00:00
-- url     : https://prove2.me/submissions/c7daabbe-a977-4cbd-b0ba-83cf857cc093

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
theorem _root_.solution {f : E → Matrix (Fin n) (Fin n) ℂ} (hf : ContDiff ℝ N f) :
    ContDiff ℝ N (fun x => (f x)ᴴ) := by
  rw [contDiff_mat_iff] at hf ⊢
  intro i j
  simp only [Matrix.conjTranspose_apply]
  exact Complex.conjCLE.contDiff.comp (hf j i)
end PI.KFinSmoothW.Gard
