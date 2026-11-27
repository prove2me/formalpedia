-- Prove2me | solution 1 for PI.Tr.dualLat_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:20:24.775801+00:00
-- url     : https://prove2.me/submissions/933a9a4e-5d34-472e-82e3-19f05c99cdec

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_DualTransport
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_InstIsZLatticeDualLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open PI PI.Tr
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace PI.Tr
theorem _root_.solution {Λ₁ Λ₂ : Submodule ℤ E} (h : Λ₁ ≤ Λ₂) : dualLat Λ₂ ≤ dualLat Λ₁ :=
  fun _ hy x hx => (show ∀ z ∈ Λ₂, ∃ n : ℤ, inner ℝ z _ = (n : ℝ) from hy) x (h hx)
end PI.Tr
