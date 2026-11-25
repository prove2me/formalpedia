-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BetaLUniq.EigA.exists_pi_b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:38:08.112854+00:00
-- url     : https://prove2.me/submissions/d2a50c5b-7110-4701-bf13-144c404b465d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BetaUniqueness_EqZeroOfNormLtOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.BetaLUniq PI.UnitaryGroupMassFormula.BetaLUniq.EigA
namespace PI.UnitaryGroupMassFormula.BetaLUniq.EigA
theorem _root_.solution {R : Type*} [CommRing R] [IsDedekindDomain R] (P : Ideal R) [hP : P.IsPrime]
    (hP0 : P ≠ ⊥) : ∃ π ∈ P, π ≠ 0 ∧ ∃ b ∉ P, ∀ p ∈ P, b * p ∈ Ideal.span {π} := by
  have hPt : P ≠ ⊤ := hP.ne_top
  have hlt : P ^ 2 < P ^ 1 := Ideal.pow_right_strictAnti P hP0 hPt (show 1 < 2 by norm_num)
  rw [pow_one] at hlt
  obtain ⟨π, hπP, hπ2⟩ := SetLike.exists_of_lt hlt
  have hπ0 : π ≠ 0 := by rintro rfl; exact hπ2 (Ideal.zero_mem _)
  have hdvd : P ∣ Ideal.span {π} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem P).mpr hπP)
  obtain ⟨Q, hQ⟩ := hdvd
  have hQP : ¬ Q ≤ P := by
    intro hle
    apply hπ2
    have : Ideal.span {π} ≤ P ^ 2 := by rw [hQ, pow_two]; exact Ideal.mul_mono_right hle
    exact this (Ideal.mem_span_singleton_self π)
  obtain ⟨b, hbQ, hbP⟩ := SetLike.not_le_iff_exists.mp hQP
  refine ⟨π, hπP, hπ0, b, hbP, fun p hp => ?_⟩
  rw [hQ, mul_comm b]
  exact Ideal.mul_mem_mul hp hbQ
end PI.UnitaryGroupMassFormula.BetaLUniq.EigA
