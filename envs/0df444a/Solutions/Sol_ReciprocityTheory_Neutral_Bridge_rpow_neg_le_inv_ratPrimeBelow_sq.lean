-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.rpow_neg_le_inv_ratPrimeBelow_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:08:01.951439+00:00
-- url     : https://prove2.me/submissions/d7879a19-4d64-4a79-b921-73db56d20a17

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TendstoPrimeIdealZetaSumUniv
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_ExistsPrimeAbsNormOfHasDirichletDensity
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_ratPrimeBelow_prime
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_ratPrimeBelow_sq_le
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_DedekindZetaReal_two_le_absNorm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge
open NumberField IsDedekindDomain Filter Topology
variable {K : Type*} [Field K] [NumberField K]
namespace ReciprocityTheory.Neutral.Bridge
theorem _root_.solution (𝔭 : HeightOneSpectrum (𝓞 K)) (h : ¬ (Ideal.absNorm 𝔭.asIdeal).Prime)
    {s : ℝ} (hs : 1 < s) :
    (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤ 1 / (ratPrimeBelow 𝔭 : ℝ) ^ 2 := by
  have hp := ratPrimeBelow_prime 𝔭
  have hsq : ((ratPrimeBelow 𝔭 : ℝ)) ^ 2 ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ) := by
    exact_mod_cast ratPrimeBelow_sq_le 𝔭 h
  have hpos : (0:ℝ) < (ratPrimeBelow 𝔭 : ℝ) ^ 2 := by
    have := hp.pos; positivity
  have h2 := ReciprocityTheory.Neutral.Bridge.DedekindZetaReal.two_le_absNorm (K := K) 𝔭
  calc (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = 1 / (Ideal.absNorm 𝔭.asIdeal : ℝ) := by rw [Real.rpow_neg_one, one_div]
    _ ≤ 1 / (ratPrimeBelow 𝔭 : ℝ) ^ 2 := one_div_le_one_div_of_le hpos hsq
end ReciprocityTheory.Neutral.Bridge
