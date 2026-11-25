-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NineStatements_exists_prime_natCast_mem_3bd80a14c2c7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:37:45.698808+00:00
-- url     : https://prove2.me/submissions/c8be9d97-fab2-43db-aa3a-f221e7a88e2f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_PNormCountBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace GroundTheory.Heights₂.Heights.NineStatements
theorem _root_.solution {R : Type*} [CommRing R] (P : Ideal R) [hP : P.IsPrime] :
    ∀ n : ℕ, n ≠ 0 → (n : R) ∈ P → ∃ p : ℕ, p.Prime ∧ (p : R) ∈ P := by
  intro n
  induction n using induction_on_primes with
  | zero => intro h; exact absurd rfl h
  | one =>
    intro _ h
    exact absurd ((Ideal.eq_top_iff_one P).mpr (by simpa using h)) hP.ne_top
  | prime_mul p a hp ih =>
    intro hpa h
    rw [Nat.cast_mul] at h
    rcases hP.mem_or_mem h with h | h
    · exact ⟨p, hp, h⟩
    · exact ih (right_ne_zero_of_mul hpa) h
end GroundTheory.Heights₂.Heights.NineStatements
