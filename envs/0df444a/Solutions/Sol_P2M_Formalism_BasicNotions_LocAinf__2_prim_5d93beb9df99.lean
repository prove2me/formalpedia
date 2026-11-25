-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_LocAinf__2_prim_5d93beb9df99
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:32:24.832882+00:00
-- url     : https://prove2.me/submissions/cba1ff0f-5588-4ca2-880f-6bf58d3fafdd

import Mathlib
import Definitions.Def_Formalism_CoboundaryTransfers_Statement
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_StatementPC
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions
open Loc
open Formalism.BasicNotions.LocAinf
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)
namespace Formalism.BasicNotions.LocAinf
theorem _root_.solution : IsPrimitiveRoot (AI.ζ 2) (l ^ 2) := by
  have hnot : ¬ AI.ζ 2 ^ l ^ 1 = 1 := by
    rw [pow_one, AI.ζ_succ 1]
    exact AI.ζ_one
  have hfin : AI.ζ 2 ^ l ^ (1 + 1) = 1 := by
    rw [show l ^ (1 + 1) = l * l by ring, pow_mul, AI.ζ_succ 1, AI.ζ_succ 0, AI.ζ_zero]
  have h := orderOf_eq_prime_pow hnot hfin
  rw [show (1 + 1 : ℕ) = 2 from rfl] at h
  rw [← h]
  exact IsPrimitiveRoot.orderOf _
end Formalism.BasicNotions.LocAinf
