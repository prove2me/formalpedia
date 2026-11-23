-- Prove2me | solution 1 for PI.TOW.combo_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:39.809729+00:00
-- url     : https://prove2.me/submissions/2ddd9556-a0b8-47f4-94c2-4a635cd1605b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_FockLin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.TOW
open PI.TO
variable {K : Type} [CommRing K] {n' k : ℕ}
namespace PI.TOW
theorem _root_.solution (G : MvPolynomial (Fin n' × Fin k) K) : combo (0 : List (Fin n' × (Fin k × Fin k)) →₀ K) G = 0 := by
  simp [combo]
end PI.TOW
