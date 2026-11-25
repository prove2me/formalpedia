-- Prove2me | solution 1 for PI.AprimeInfG.restrict_embed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:37:25.434736+00:00
-- url     : https://prove2.me/submissions/839dee2a-12b1-4fde-a772-315bd9bd283b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_BlockEmb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.AprimeInfG
open scoped Matrix
variable {n k : ℕ} {S : Finset (Fin n)}
private theorem emb0_apply_coe_coe (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) (a b : Fin k) :
    emb0 e X (e a) (e b) = X a b := by
  simp [emb0]
end PI.AprimeInfG
end
end

set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfG
open scoped Matrix
variable {n k : ℕ} {S : Finset (Fin n)}
namespace PI.AprimeInfG
theorem _root_.solution (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) : resB e (emb0 e X) = X := by
  ext a b
  exact emb0_apply_coe_coe e X a b
end PI.AprimeInfG
