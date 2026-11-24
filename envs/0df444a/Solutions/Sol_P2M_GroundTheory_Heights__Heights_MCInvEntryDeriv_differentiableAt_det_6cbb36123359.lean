-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCInvEntryDeriv_differentiableAt_det_6cbb36123359
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:04:12.211859+00:00
-- url     : https://prove2.me/submissions/b5003c0c-dde7-4b56-9fcc-5a902fc9271a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PInvEntryDeriv

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
open Matrix Topology
open GroundTheory.Heights₂.Heights.MCInvEntryDeriv
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : ℕ}
namespace GroundTheory.Heights₂.Heights.MCInvEntryDeriv
theorem _root_.solution {M : E → Matrix (Fin g) (Fin g) ℝ} {p : E}
    (hM : ∀ j l, DifferentiableAt ℝ (fun q => M q j l) p) :
    DifferentiableAt ℝ (fun q => (M q).det) p := by
  simp only [det_apply, Units.smul_def, zsmul_eq_mul]
  exact DifferentiableAt.fun_sum fun σ _ =>
    (differentiableAt_const _).mul
      (HasFDerivAt.finsetProd (u := Finset.univ) (g := fun i q => M q (σ i) i)
        fun i _ => (hM _ _).hasFDerivAt).differentiableAt
end GroundTheory.Heights₂.Heights.MCInvEntryDeriv
