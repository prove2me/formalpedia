-- Prove2me | solution 1 for P2M_Formalism_QuantumDeterminants_WirtingerDerivatives_top_ne_zero__646af485dac4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:47:28.660589+00:00
-- url     : https://prove2.me/submissions/43a56f71-288a-4eaa-b576-a322f8564d3f

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
open Filter
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.WirtingerDerivatives
variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.QuantumDeterminants.WirtingerDerivatives
theorem _root_.solution : (∞ : ℕ∞ω) ≠ 0 := by
  exact WithTop.coe_ne_zero.mpr (by simp)
end Formalism.QuantumDeterminants.WirtingerDerivatives
