-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.card_fiber_ratPrimeBelow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:01:58.766913+00:00
-- url     : https://prove2.me/submissions/3f9a6dc4-7ae7-43c4-b234-4c7b04300790

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TendstoPrimeIdealZetaSumUniv
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_ExistsPrimeAbsNormOfHasDirichletDensity
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_mem_primesOverFinset_ratPrimeBelow
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_card_primesOverFinset_span_le_finrank

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
theorem _root_.solution {ι : Type*} (g : ι → HeightOneSpectrum (𝓞 K)) (hg : Function.Injective g)
    (F : Finset ι) (p : ℕ) (hp : p.Prime) :
    (F.filter fun x => ratPrimeBelow (g x) = p).card ≤ Module.finrank ℚ K := by
  calc (F.filter fun x => ratPrimeBelow (g x) = p).card
      ≤ (IsDedekindDomain.primesOverFinset (Ideal.span {(p:ℤ)}) (𝓞 K)).card := by
        apply Finset.card_le_card_of_injOn (fun x => (g x).asIdeal)
        · intro x hx
          have hx' : x ∈ F.filter (fun x => ratPrimeBelow (g x) = p) := hx
          have h2 := (Finset.mem_filter.1 hx').2
          have h3 := mem_primesOverFinset_ratPrimeBelow (g x)
          rw [h2] at h3
          exact h3
        · intro x _ y _ hxy
          exact hg (HeightOneSpectrum.ext hxy)
    _ ≤ _ := card_primesOverFinset_span_le_finrank (K := K) p hp
end ReciprocityTheory.Neutral.Bridge
