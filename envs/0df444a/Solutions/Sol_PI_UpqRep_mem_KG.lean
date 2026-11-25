-- Prove2me | solution 1 for PI.UpqRep.mem_KG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:49:11.17022+00:00
-- url     : https://prove2.me/submissions/c93117d3-14f9-48b2-8af2-970a1b84e560

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Finset Topology
open scoped InnerProductSpace ContDiff
noncomputable section
open PI PI.UpqRep
namespace PI.UpqRep
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (g : UJ ε) : g ∈ KG ε ↔ toM g ∈ Kset ε := Iff.rfl
end PI.UpqRep
