-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.tendsto_primeIdealZetaSum_univ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:50:27.836681+00:00
-- url     : https://prove2.me/submissions/fbd3fd60-d4d4-4b63-b380-798ff6811640

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TendstoPrimeIdealZetaSumUniv
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_DedekindZetaReal_tendsto_zetaReal
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_DedekindZetaReal_zetaReal_le_exp

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
namespace ReciprocityTheory.Neutral.Bridge
theorem _root_.solution :
    Tendsto (fun s : ℝ => NumberField.Set.primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s) (𝓝[>] 1) atTop := by
  have h1 : Tendsto (fun s ↦ Real.log (zetaReal K s) / 2) (𝓝[>] 1) atTop :=
    (Real.tendsto_log_atTop.comp (tendsto_zetaReal K)).atTop_div_const two_pos
  refine tendsto_atTop_mono' _ ?_ h1
  filter_upwards [self_mem_nhdsWithin, (tendsto_zetaReal K).eventually_gt_atTop 0]
    with s (hs : 1 < s) hpos
  have e : (∑' 𝔭 : (Set.univ : Set (HeightOneSpectrum (𝓞 K))),
      (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)) =
      ∑' 𝔭 : HeightOneSpectrum (𝓞 K), (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) :=
    tsum_univ (fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦ (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))
  rw [NumberField.Set.primeIdealZetaSum_def, e]
  have := (Real.log_le_iff_le_exp hpos).mpr (zetaReal_le_exp K hs)
  linarith
end ReciprocityTheory.Neutral.Bridge
