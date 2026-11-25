-- Prove2me | solution 1 for PI.VolStabW.FiniteFieldCounting.prod_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:56:45.882791+00:00
-- url     : https://prove2.me/submissions/513ac2cc-d805-483e-84db-6e747681036d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open PI.VolStabW.FiniteFieldCounting
namespace PI.VolStabW.FiniteFieldCounting
theorem _root_.solution {ι : Type} (δ : ι → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h : ∀ j, |δ j| ≤ t) (s : Finset ι) :
    |∏ j ∈ s, (1 + δ j) - 1| ≤ t * (2 ^ s.card - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.card_insert_of_notMem hj]
    set P := ∏ j ∈ s, (1 + δ j)
    have hP : |P| ≤ 1 + |P - 1| := by
      have := abs_sub_abs_le_abs_sub P 1
      rw [abs_one] at this
      linarith
    have e : (1 + δ j) * P - 1 = (P - 1) + δ j * P := by ring
    rw [e]
    have h1 := abs_add_le (P - 1) (δ j * P)
    rw [abs_mul] at h1
    have hpow : (2 : ℝ) ^ (s.card + 1) = 2 * 2 ^ s.card := by ring
    rw [hpow]
    have h2 : |δ j| * |P| ≤ t * (1 + |P - 1|) := mul_le_mul (h j) hP (abs_nonneg _) ht0
    have h3 : 0 ≤ |P - 1| := abs_nonneg _
    nlinarith [mul_nonneg (sub_nonneg.mpr ht1) h3]
end PI.VolStabW.FiniteFieldCounting
