-- Prove2me | solution 1 for PI.AlgValsFin.W.mem_compo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:19:14.489626+00:00
-- url     : https://prove2.me/submissions/17f5ec0a-002d-4d5f-bde0-9bfcbaad6997

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_IsIntegralOfMemCompo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]
namespace PI.AlgValsFin.W
theorem _root_.solution (φ : L →+* ℂ) (x : L) : φ x ∈ compo L :=
  (le_iSup (fun ψ : L →+* ℂ => ψ.toRatAlgHom.fieldRange) φ) (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩)
end PI.AlgValsFin.W
