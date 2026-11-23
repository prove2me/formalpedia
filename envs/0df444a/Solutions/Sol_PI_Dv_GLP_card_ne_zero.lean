-- Prove2me | solution 1 for PI.Dv.GLP.card_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:04.358799+00:00
-- url     : https://prove2.me/submissions/865429ce-8bad-43a1-8039-152bdde22c3f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_FinrankIntertw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLP
open Representation
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.GLP
theorem _root_.solution [CharZero K] : ((Fintype.card G : ℕ) : K) ≠ 0 :=
  Nat.cast_ne_zero.2 Fintype.card_ne_zero
end PI.Dv.GLP
