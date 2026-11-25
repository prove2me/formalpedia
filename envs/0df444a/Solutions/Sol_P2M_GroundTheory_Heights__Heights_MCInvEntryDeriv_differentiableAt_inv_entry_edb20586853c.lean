-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCInvEntryDeriv_differentiableAt_inv_entry_edb20586853c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:57:10.301037+00:00
-- url     : https://prove2.me/submissions/c1116f16-9bdf-4058-8bdd-66aff5197dcf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PInvEntryDeriv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCInvEntryDeriv_differentiableAt_det_6cbb36123359
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCInvEntryDeriv_inv_entry_eq_c0f1905f6b53

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
theorem _root_.solution {Y : E → Matrix (Fin g) (Fin g) ℝ} {p : E}
    (hY : ∀ j l, DifferentiableAt ℝ (fun q => Y q j l) p) (hdet : (Y p).det ≠ 0) (j l : Fin g) :
    DifferentiableAt ℝ (fun q => (Y q)⁻¹ j l) p := by
  simp only [inv_entry_eq]
  refine ((differentiableAt_det hY).inv hdet).mul (differentiableAt_det fun k m => ?_)
  simp only [updateRow_apply]
  split_ifs
  · exact differentiableAt_const _
  · exact hY k m
end GroundTheory.Heights₂.Heights.MCInvEntryDeriv
