-- Prove2me | solution 1 for PI.AprimeInfW.reim_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:19:18.798928+00:00
-- url     : https://prove2.me/submissions/9f50a059-2375-4eb7-ba90-a819e673f47d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_DetMulRCReal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_MpOfIsomProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfW
open MeasureTheory Matrix ComplexConjugate
namespace PI.AprimeInfW
theorem _root_.solution {n m : ℕ} (y : EuclideanSpace ℝ (Fin n × Fin m × Bool)) :
    ∃ Y : Matrix (Fin n) (Fin m) ℂ, reim Y = y := by
  refine ⟨Matrix.of fun i j => ⟨y.ofLp (i, j, true), y.ofLp (i, j, false)⟩, ?_⟩
  ext p
  rcases p with ⟨i, j, s⟩
  cases s <;> simp [reim]
end PI.AprimeInfW
