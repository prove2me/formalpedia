-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.summable_absNorm_rpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:25:20.840802+00:00
-- url     : https://prove2.me/submissions/764fdc48-e5fb-4344-9360-6481fd660476

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TendstoPrimeIdealZetaSumUniv
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_DedekindZetaReal_sum_le_zetaReal

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
theorem _root_.solution {s : ℝ} (hs : 1 < s) :
    Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) => (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) := by
  classical
  refine summable_of_sum_le (c := zetaReal K s) (fun _ ↦ by positivity) fun u ↦ ?_
  rw [← Finset.sum_image (f := fun I : Ideal (𝓞 K) ↦ (Ideal.absNorm I : ℝ) ^ (-s))
    (g := HeightOneSpectrum.asIdeal) (fun v _ w _ h ↦ HeightOneSpectrum.ext h)]
  exact sum_le_zetaReal K hs _
end ReciprocityTheory.Neutral.Bridge
