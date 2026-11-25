-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.DedekindZetaReal.summable_zetaReal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:55:45.647294+00:00
-- url     : https://prove2.me/submissions/7d94cb03-d7de-42ad-a4fc-e441897c3ba2

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TendstoPrimeIdealZetaSumUniv
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_DedekindZetaReal_zetaReal_tendsto_sum_card_div
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_DedekindZetaReal_zetaReal_term_eq

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
open ReciprocityTheory.Neutral.Bridge.DedekindZetaReal
namespace ReciprocityTheory.Neutral.Bridge.DedekindZetaReal
theorem _root_.solution {s : ℝ} (hs : 1 < s) :
    Summable fun n : ℕ =>
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s) := by
  obtain ⟨c, hc⟩ := zetaReal_tendsto_sum_card_div K
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ))
      =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
    simp_rw [Real.rpow_one]
    refine Asymptotics.isBigO_of_div_tendsto_nhds ?_ c hc
    filter_upwards [eventually_ne_atTop 0] with n hn h
    exact absurd h (Nat.cast_ne_zero.mpr hn)
  have := LSeriesSummable_of_sum_norm_bigO_and_nonneg hO (fun _ ↦ Nat.cast_nonneg _) zero_le_one
    (s := (s : ℂ)) (by simpa using hs)
  unfold LSeriesSummable at this
  have h2 := (funext (zetaReal_term_eq K (zero_lt_one.trans hs)))
  simp only [Complex.ofReal_natCast] at this h2
  rw [h2] at this
  exact Complex.summable_ofReal.mp this
end ReciprocityTheory.Neutral.Bridge.DedekindZetaReal
