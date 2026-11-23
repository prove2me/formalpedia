-- Prove2me | solution 1 for PI.SelfDualLoc.W.ND.mem_intOE_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:26:53.379613+00:00
-- url     : https://prove2.me/submissions/4ae049f4-42e6-4c1f-b50e-4cb45d95ac5b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_DualBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_Nondeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct nonZeroDivisors
noncomputable section
open PI PI.SelfDualLoc PI.SelfDualLoc.W PI.SelfDualLoc.W.ND
open PI.SelfDualLoc
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
namespace PI.SelfDualLoc.W.ND
theorem _root_.solution (x : E) : x ∈ intOE E ↔ ∃ a : 𝓞 E, (a : E) = x := by
  unfold intOE
  exact RingHom.mem_range
end PI.SelfDualLoc.W.ND
