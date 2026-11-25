-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.DedekindZetaReal.sum_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:32:49.982927+00:00
-- url     : https://prove2.me/submissions/a191dca5-5e8c-4c05-99c5-b40c866bbe3a

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TendstoPrimeIdealZetaSumUniv
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_DedekindZetaReal_sum_le_prod_geom
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_summable_absNorm_rpow
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_DedekindZetaReal_two_le_absNorm
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_DedekindZetaReal_geom_le_exp

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
variable (K : Type*) [Field K] [NumberField K]
open DedekindZetaReal
open ReciprocityTheory.Neutral.Bridge.DedekindZetaReal
namespace ReciprocityTheory.Neutral.Bridge.DedekindZetaReal
theorem _root_.solution {s : ℝ} (hs : 1 < s) (T : Finset (Ideal (𝓞 K))) :
    ∑ I ∈ T, (Ideal.absNorm I : ℝ) ^ (-s) ≤
      Real.exp (2 * ∑' 𝔭 : HeightOneSpectrum (𝓞 K), (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) := by
  obtain ⟨P, B, hPB⟩ := sum_le_prod_geom K (zero_lt_one.trans hs) T
  refine hPB.trans ?_
  have hx : ∀ v : HeightOneSpectrum (𝓞 K), (Ideal.absNorm v.asIdeal : ℝ) ^ (-s) ≤ 1 / 2 := by
    intro v
    have h2 := two_le_absNorm K v
    calc (Ideal.absNorm v.asIdeal : ℝ) ^ (-s) ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = 1 / (Ideal.absNorm v.asIdeal : ℝ) := by rw [Real.rpow_neg_one, one_div]
      _ ≤ 1 / 2 := one_div_le_one_div_of_le two_pos h2
  calc ∏ v ∈ P, ∑ k ∈ Finset.range (B + 1), ((Ideal.absNorm v.asIdeal : ℝ) ^ (-s)) ^ k
      ≤ ∏ v ∈ P, Real.exp (2 * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s)) :=
        Finset.prod_le_prod (fun v _ ↦ Finset.sum_nonneg fun k _ ↦ by positivity)
          fun v _ ↦ geom_le_exp (by positivity) (hx v) B
    _ = Real.exp (2 * ∑ v ∈ P, (Ideal.absNorm v.asIdeal : ℝ) ^ (-s)) := by
        rw [Finset.mul_sum, Real.exp_sum]
    _ ≤ _ := by
        refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ two_pos.le)
        exact (summable_absNorm_rpow K hs).sum_le_tsum P fun _ _ ↦ by positivity
end ReciprocityTheory.Neutral.Bridge.DedekindZetaReal
