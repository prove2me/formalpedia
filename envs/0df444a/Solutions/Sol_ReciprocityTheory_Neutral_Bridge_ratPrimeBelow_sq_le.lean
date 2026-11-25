-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.ratPrimeBelow_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:55:54.757447+00:00
-- url     : https://prove2.me/submissions/a446ece8-d379-48e9-9324-73e572c2a148

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TendstoPrimeIdealZetaSumUniv
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_ExistsPrimeAbsNormOfHasDirichletDensity
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_ratPrimeBelow_prime
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_absNorm_eq_ratPrimeBelow_pow
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
theorem _root_.solution (𝔭 : HeightOneSpectrum (𝓞 K)) (h : ¬ (Ideal.absNorm 𝔭.asIdeal).Prime) :
    ratPrimeBelow 𝔭 ^ 2 ≤ Ideal.absNorm 𝔭.asIdeal := by
  obtain ⟨f, hf⟩ := absNorm_eq_ratPrimeBelow_pow 𝔭
  have hp := ratPrimeBelow_prime 𝔭
  have h2 : 2 ≤ Ideal.absNorm 𝔭.asIdeal := by
    exact_mod_cast ReciprocityTheory.Neutral.Bridge.DedekindZetaReal.two_le_absNorm (K := K) 𝔭
  rw [hf] at h h2 ⊢
  rcases f with _ | _ | f
  · simp at h2
  · exact (h (by simpa using hp)).elim
  · exact Nat.pow_le_pow_right hp.pos (by omega)
end ReciprocityTheory.Neutral.Bridge
