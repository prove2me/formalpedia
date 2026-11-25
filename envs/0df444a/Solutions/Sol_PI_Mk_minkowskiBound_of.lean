-- Prove2me | solution 1 for PI.Mk.minkowskiBound_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:04:31.496973+00:00
-- url     : https://prove2.me/submissions/ad02dd58-992a-456d-9bf5-4e1f4f74e962

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Minkowski
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSumStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_Assemble
import Theorems.Thm_PI_Mk_padicValNat_pow_mul_factorial
import Theorems.Thm_PI_Mk_pow_minkowskiExp_dvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Mk
open Finset
namespace PI.Mk
theorem _root_.solution (h : PGroupStep) : PI.MinkowskiBound := by
  intro N G hG
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro ℓ k hℓ hk
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime ℓ hk
  have hinj : Function.Injective G.subtype := G.subtype_injective
  have hcard : Nat.card (K.map G.subtype) = ℓ ^ k := by
    rw [Subgroup.card_map_of_injective hinj, hK]
  have hfin : Finite (K.map G.subtype) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hℓ.ne_zero)
  have hp : IsPGroup ℓ (K.map G.subtype) := IsPGroup.of_card hcard
  have hdvd := h N ℓ hℓ (K.map G.subtype) hfin hp
  rw [hcard] at hdvd
  have hne : ℓ ^ (N / (ℓ - 1)) * (N / (ℓ - 1)).factorial ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hℓ.ne_zero) (Nat.factorial_ne_zero _)
  have hle : k ≤ PI.minkowskiExp N ℓ := by
    rw [← padicValNat_pow_mul_factorial N ℓ hℓ]
    exact (padicValNat_dvd_iff_le hne).1 hdvd
  exact (pow_dvd_pow ℓ hle).trans (pow_minkowskiExp_dvd N ℓ hℓ)
end PI.Mk
