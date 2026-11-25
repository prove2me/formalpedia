-- Prove2me | solution 1 for PI.ArtSch.WittLiftWork.sub_mem_of_coeff_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:34:27.84771+00:00
-- url     : https://prove2.me/submissions/25eb36b6-5b7e-48a5-8891-c514e341a5f3

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
theorem _root_.solution {n : ℕ} {a b : WittVector p k} (h : ∀ i < n, a.coeff i = b.coeff i) :
    a - b ∈ I n := by
  rw [RingHom.mem_ker, map_sub, sub_eq_zero]
  refine TruncatedWittVector.ext fun i => ?_
  simpa [WittVector.coeff_truncate] using h i i.2
end PI.ArtSch.WittLiftWork
