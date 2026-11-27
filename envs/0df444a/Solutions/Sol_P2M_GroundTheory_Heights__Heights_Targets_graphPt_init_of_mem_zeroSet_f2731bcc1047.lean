-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_graphPt_init_of_mem_zeroSet_f2731bcc1047
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:08:39.062289+00:00
-- url     : https://prove2.me/submissions/61ad9348-4947-4866-9503-b96c35871ed5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_GraphIdeal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_graphHom_X_last_02e1f6eebe08
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_graphHom_rename_9e3a36680299

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet)
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.Targets
theorem _root_.solution {J : Ideal (MvPolynomial (Fin n) ℂ)} (p : MvPolynomial (Fin n) ℂ)
    {x : Fin (n + 1) → ℂ} (hx : x ∈ zeroSet (graphIdeal J p)) : graphPt p (Fin.init x) = x := by
  have h := hx (X (Fin.last n) - rename Fin.castSucc p)
    (by rw [graphIdeal, Ideal.mem_comap, map_sub, graphHom_X_last, graphHom_rename, sub_self]; exact J.zero_mem)
  rw [map_sub, eval_X, eval_rename, sub_eq_zero] at h
  rw [graphPt]
  conv_rhs => rw [← Fin.snoc_init_self x]
  rw [h]
  rfl
end GroundTheory.Heights₂.Heights.Targets
