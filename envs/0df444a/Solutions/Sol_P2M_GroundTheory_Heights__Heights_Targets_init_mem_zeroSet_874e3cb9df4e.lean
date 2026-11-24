-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_init_mem_zeroSet_874e3cb9df4e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:15.053393+00:00
-- url     : https://prove2.me/submissions/fd6788f3-c11d-4693-a1b6-a81e9dafcfc5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_GraphIdeal
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
    {x : Fin (n + 1) → ℂ} (hx : x ∈ zeroSet (graphIdeal J p)) : Fin.init x ∈ zeroSet J := by
  intro q hq
  have h := hx (rename Fin.castSucc q) (by rw [graphIdeal, Ideal.mem_comap, graphHom_rename]; exact hq)
  rw [eval_rename] at h
  exact h
end GroundTheory.Heights₂.Heights.Targets
