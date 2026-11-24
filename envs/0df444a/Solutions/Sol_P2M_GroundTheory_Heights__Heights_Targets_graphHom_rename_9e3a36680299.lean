-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_graphHom_rename_9e3a36680299
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:07.659804+00:00
-- url     : https://prove2.me/submissions/2ba434c7-a5ea-42be-8141-29f690f08611

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_GraphIdeal

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
theorem _root_.solution (p q : MvPolynomial (Fin n) ℂ) : graphHom p (rename Fin.castSucc q) = q := by
  rw [graphHom, aeval_rename]
  have : (Fin.snoc (X : Fin n → MvPolynomial (Fin n) ℂ) p : Fin (n + 1) → MvPolynomial (Fin n) ℂ) ∘ Fin.castSucc = X :=
    funext fun i => by simp
  rw [this, aeval_X_left_apply]
end GroundTheory.Heights₂.Heights.Targets
