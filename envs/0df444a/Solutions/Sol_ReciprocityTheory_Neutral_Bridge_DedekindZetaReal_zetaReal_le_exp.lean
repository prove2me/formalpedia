-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.DedekindZetaReal.zetaReal_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:41:29.245805+00:00
-- url     : https://prove2.me/submissions/2ad7fb6f-63a3-41fe-8866-96d14b583543

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TendstoPrimeIdealZetaSumUniv
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_DedekindZetaReal_sum_le_exp
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_DedekindZetaReal_sum_card_eq

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
theorem _root_.solution {s : ℝ} (hs : 1 < s) :
    zetaReal K s ≤
      Real.exp (2 * ∑' 𝔭 : HeightOneSpectrum (𝓞 K), (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) := by
  refine Real.tsum_le_of_sum_le (fun n ↦ by positivity) fun u ↦ ?_
  rw [sum_card_eq]
  exact sum_le_exp K hs _
end ReciprocityTheory.Neutral.Bridge.DedekindZetaReal
