-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_pow_add_le_abec59476fd6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:13:42.978959+00:00
-- url     : https://prove2.me/submissions/d40b1fd3-5c4c-4ee3-8d80-9280ed06a8d4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropTermSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropHilbWSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountDrop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open Filter
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.SectionCount GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop
theorem _root_.solution (c n : ℝ) (hc : 0 ≤ c) (hn : 1 ≤ n) :
    ∀ e : ℕ, (n + c) ^ e ≤ n ^ e + ((1 + c) ^ e - 1) * (n ^ e / n)
  | 0 => by simp
  | e + 1 => by
    have ih := solution c n hc hn e
    have hn0 : 0 < n := by linarith
    have hA : 0 ≤ (1 + c) ^ e - 1 := by
      have : 1 ≤ (1 + c) ^ e := one_le_pow₀ (by linarith)
      linarith
    have hq : n ^ e / n ≤ n ^ e := div_le_self (by positivity) hn
    have hq' : n ^ (e + 1) / n = n ^ e := by
      rw [pow_succ]; field_simp
    have hqn : n ^ e / n * n = n ^ e := by field_simp
    have h1 : (n + c) ^ e * (n + c) ≤ (n ^ e + ((1 + c) ^ e - 1) * (n ^ e / n)) * (n + c) :=
      mul_le_mul_of_nonneg_right ih (by linarith)
    have h2 : ((1 + c) ^ e - 1) * c * (n ^ e / n) ≤ ((1 + c) ^ e - 1) * c * n ^ e :=
      mul_le_mul_of_nonneg_left hq (mul_nonneg hA hc)
    rw [hq', pow_succ, pow_succ, pow_succ]
    nlinarith [h1, h2, hqn]
end GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop
