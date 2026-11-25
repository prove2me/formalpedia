-- Prove2me | solution 1 for PI.BeDiagZp.SubstW.deg_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:34:07.704444+00:00
-- url     : https://prove2.me/submissions/0f46db6a-6617-405e-8ced-3fde09d98bbe

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_PowerSeriesDiagonalLinear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.BeDiagZp PI.BeDiagZp.SubstW
variable {p : ℕ} [Fact p.Prime]
namespace PI.BeDiagZp.SubstW
theorem _root_.solution {σ : Type*} (α : σ →₀ ℕ) : (α.sum fun _ k => k) = α.degree := by
  rw [Finsupp.degree_apply]
  rfl
end PI.BeDiagZp.SubstW
