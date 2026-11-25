-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.coeff_mul_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:34:13.149334+00:00
-- url     : https://prove2.me/submissions/1ce7d956-4e94-40e2-b360-8c327c308bb6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEisInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDeltaInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (V G : PowerSeries ℂ) (hV : PowerSeries.coeff 0 V = 1) (n : ℕ)
    (hG : ∀ i < n, PowerSeries.coeff i G = 0) :
    (∀ i < n, PowerSeries.coeff i (V * G) = 0) ∧
      PowerSeries.coeff n (V * G) = PowerSeries.coeff n G := by
  constructor
  · intro i hi
    rw [PowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [hG x.2 (by omega), mul_zero]
  · rw [PowerSeries.coeff_mul, Finset.sum_eq_single (0, n)]
    · rw [hV, one_mul]
    · intro x hx hne
      obtain ⟨a, b⟩ := x
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      have hb : b < n := by
        by_contra hb'
        apply hne
        have ha0 : a = 0 := by simp only at hx; omega
        have hbn : b = n := by simp only at hx; omega
        rw [ha0, hbn]
      rw [hG b hb, mul_zero]
    · intro h
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp)) h
end ReciprocityTheory.ChartRestriction.L1
