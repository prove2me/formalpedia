-- Prove2me | solution 1 for PI.ScRefExists.ApP.natCast_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:24:32.352809+00:00
-- url     : https://prove2.me/submissions/d846b624-c9b8-495f-9679-37aa852e7865

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PPAssemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PrincipalIdealRingAtPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct nonZeroDivisors
open PI PI.ScRefExists PI.ScRefExists.ApP
open PI.ScRefExists.Sk
namespace PI.ScRefExists.ApP
theorem _root_.solution {p : ℕ} (hp : p.Prime) {s : ℕ} (hs : Nat.Coprime s p) : (s : ℤ) ∉ Pz p := by
  rw [Ideal.mem_span_singleton]
  intro h
  have h1 : p ∣ s := Int.natCast_dvd_natCast.mp h
  have h2 : p ∣ Nat.gcd s p := Nat.dvd_gcd h1 dvd_rfl
  rw [Nat.Coprime.gcd_eq_one hs] at h2
  exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
end PI.ScRefExists.ApP
