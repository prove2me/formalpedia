-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_alt_sum_e5d5b5b56ff0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:29:37.075296+00:00
-- url     : https://prove2.me/submissions/6116e970-5130-4af2-8e8e-2ad2a6c60f7f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_DegZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CohMkEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.EulerSES
open Module
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.EulerSES
theorem _root_.solution (a b c i p r : ℕ → ℤ) (h0 : a 0 = i 0) (hs : ∀ n, a (n + 1) = i (n + 1) + r n)
    (hb : ∀ n, b n = p n + i n) (hc : ∀ n, c n = r n + p n) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * b n =
      ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * a n + ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * c n +
        (-1) ^ (N + 1) * r N := by
  induction N with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul, pow_one]
    rw [hb, hc, h0]
    ring
  | succ N ih =>
    simp only [Finset.sum_range_succ _ (N + 1)]
    rw [ih, hs N, hb (N + 1), hc (N + 1)]
    ring
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.EulerSES
