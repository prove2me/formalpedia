-- Prove2me | solution 1 for PI.VolStabS.FiniteFieldCounting.prod_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:49:55.917412+00:00
-- url     : https://prove2.me/submissions/49060ddd-3968-4c72-9191-a1857db18d9a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
open PI.VolStabS.FiniteFieldCounting
namespace PI.VolStabS.FiniteFieldCounting
theorem _root_.solution {ι : Type} (δ : ι → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h : ∀ j, |δ j| ≤ t) (s : Finset ι) :
    |∏ j ∈ s, (1 + δ j) - 1| ≤ t * (2 ^ s.card - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have h1 : |∏ j ∈ s, (1 + δ j)| ≤ 1 + t * (2 ^ s.card - 1) := by
      have := abs_sub_abs_le_abs_sub (∏ j ∈ s, (1 + δ j)) 1
      rw [abs_one] at this
      linarith
    have hpow : (1 : ℝ) ≤ 2 ^ s.card := one_le_pow₀ (by norm_num)
    have h2 : |δ a * ∏ j ∈ s, (1 + δ j)| ≤ t * (1 + t * (2 ^ s.card - 1)) := by
      rw [abs_mul]
      exact mul_le_mul (h a) h1 (abs_nonneg _) ht0
    have h3 : (1 + δ a) * ∏ j ∈ s, (1 + δ j) - 1 =
        (∏ j ∈ s, (1 + δ j) - 1) + δ a * ∏ j ∈ s, (1 + δ j) := by ring
    rw [h3]
    have h4 : t * (t * (2 ^ s.card - 1)) ≤ t * (2 ^ s.card - 1) := by
      apply mul_le_mul_of_nonneg_left _ ht0
      nlinarith
    calc |(∏ j ∈ s, (1 + δ j) - 1) + δ a * ∏ j ∈ s, (1 + δ j)|
        ≤ |∏ j ∈ s, (1 + δ j) - 1| + |δ a * ∏ j ∈ s, (1 + δ j)| := abs_add_le _ _
      _ ≤ t * (2 ^ s.card - 1) + t * (1 + t * (2 ^ s.card - 1)) := add_le_add ih h2
      _ ≤ t * (2 ^ (s.card + 1) - 1) := by
          rw [pow_succ]
          nlinarith
end PI.VolStabS.FiniteFieldCounting
