-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_dvd_of_forall_emultiplicity_le_e0492f3f8d14
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:30:39.489633+00:00
-- url     : https://prove2.me/submissions/a107ea19-22b2-49a8-a415-7837675b4642

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormSection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {F : Type*} [Field F] {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] {a b : R} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ p, Irreducible p → emultiplicity p a ≤ emultiplicity p b) : a ∣ b := by
  induction a using UniqueFactorizationMonoid.induction_on_prime generalizing b with
  | h₁ => exact absurd rfl ha
  | h₂ x hx => exact hx.dvd
  | h₃ a p ha' hp ih =>
    have hpp : emultiplicity p p = 1 :=
      (FiniteMultiplicity.of_not_isUnit hp.not_isUnit hp.ne_zero).emultiplicity_self
    have hpb : p ∣ b := by
      apply dvd_of_emultiplicity_pos
      have := h p hp.irreducible
      rw [emultiplicity_mul hp, hpp] at this
      exact lt_of_lt_of_le (by simp) this
    obtain ⟨b', rfl⟩ := hpb
    have hb' : b' ≠ 0 := right_ne_zero_of_mul hb
    refine mul_dvd_mul_left p (ih ha' hb' fun q hq => ?_)
    have hqp : Prime q := hq.prime
    have hfin : emultiplicity q p ≠ ⊤ := by
      rw [Ne, emultiplicity_eq_top, not_not]
      exact FiniteMultiplicity.of_not_isUnit hqp.not_isUnit hp.ne_zero
    have := h q hq
    rw [emultiplicity_mul hqp, emultiplicity_mul hqp] at this
    exact (WithTop.add_le_add_iff_left hfin).mp this
end GroundTheory.Heights₂.Heights
