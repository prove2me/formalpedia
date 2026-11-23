-- Prove2me | solution 1 for PI.ArtSch.WittLiftWork.coeff_eq_of_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:53.419665+00:00
-- url     : https://prove2.me/submissions/c1c52cb9-12c8-481d-b290-300ffc1b79fd

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
theorem _root_.solution {n : ℕ} {a b : WittVector p k} (hab : a - b ∈ I n) {i : ℕ} (hi : i < n) :
    a.coeff i = b.coeff i := by
  have h0 := RingHom.mem_ker.1 hab
  rw [map_sub, sub_eq_zero] at h0
  have h1 := congrArg (TruncatedWittVector.coeff ⟨i, hi⟩) h0
  simpa [WittVector.coeff_truncate] using h1
end PI.ArtSch.WittLiftWork
