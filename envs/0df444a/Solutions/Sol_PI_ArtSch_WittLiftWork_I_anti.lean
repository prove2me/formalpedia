-- Prove2me | solution 1 for PI.ArtSch.WittLiftWork.I_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:34:18.561158+00:00
-- url     : https://prove2.me/submissions/676ff6d9-27be-41bf-b8ad-4aceb9da4fdf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ArtSch
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittCoefficients_CoeffEqOfSubMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.ArtSch PI.ArtSch.WittLiftWork
open WittVector
variable {p : ℕ} [hp : Fact p.Prime] {k : Type} [CommRing k]
namespace PI.ArtSch.WittLiftWork
theorem _root_.solution {m n : ℕ} (h : n ≤ m) {x : WittVector p k} (hx : x ∈ I m) : x ∈ I n :=
  mem_I.2 fun i hi => mem_I.1 hx i (Nat.lt_of_lt_of_le hi h)
end PI.ArtSch.WittLiftWork
