-- Prove2me | solution 1 for UpperTheory.exists_maxFlow_attained_and_isOptDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:10:27.947371+00:00
-- url     : https://prove2.me/submissions/51b01af9-6e52-4903-b808-654e52df2bdc

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_MaxFlowValueAttained
import Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_ExistsMaxFlowAttainedAndIsOptDual
import Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_exists_opt_flow
import Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_maxFlow_eq
import Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_strong


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Formalism.IncomingBounds
namespace UpperTheory
theorem _root_.solution :
    ∀ (l d : ℕ) [NeZero d], 3 ≤ l → ∀ D : ZMod d → ℝ, 0 ≤ D →
    (∃ x, IsFlow l d D x ∧ flowVal d x = maxFlow l d D) ∧ ∃ sig, IsOptDual l d D sig := by
  intro l d _ hl D hD
  have hl1 : 1 ≤ l := by omega
  obtain ⟨x, hx, hmax⟩ := FlowLoadBounds.exists_opt_flow hl1 D hD
  obtain ⟨σ, hσ, hsum⟩ := FlowLoadBounds.strong hl1 D hD
  refine ⟨⟨x, hx, (FlowLoadBounds.maxFlow_eq hx hmax).symm⟩, σ, hσ, ?_⟩
  rw [Fnum, ← hsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring
end UpperTheory
