-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_cond_ins_9efaac490a1c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:11.837886+00:00
-- url     : https://prove2.me/submissions/cadc7f53-0009-4553-a5e6-00a2be7fc47b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombContractSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHCombContract

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.KHCombContract
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
variable {S : Type} [CommRing S]
namespace GroundTheory.Heights₂.Heights.Kleiman.KHCombContract
theorem _root_.solution (J : ∀ k, Finset (ι k)) (d : ℕ) (k : K) (i₀ : ι k) (T : ∀ k, Finset (ι k)) (h0 : i₀ ∉ T k)
    (h : ((∀ l, (T l).Nonempty) ∧ ∑ l, ((T l).card - 1) = d) ∧ ∀ l, J l ⊆ T l) :
    ((∀ l, (ins k i₀ T l).Nonempty) ∧ ∑ l, ((ins k i₀ T l).card - 1) = d + 1) ∧ ∀ l, J l ⊆ ins k i₀ T l := by
  obtain ⟨⟨hne, hsum⟩, hJ⟩ := h
  refine ⟨⟨fun l => ?_, ?_⟩, fun l => ?_⟩
  · by_cases hl : l = k
    · subst hl; rw [ins, Function.update_self]; exact Finset.insert_nonempty _ _
    · rw [ins, Function.update_of_ne hl]; exact hne l
  · have h1 := sum_card_update_of_mem T k (insert i₀ (T k)) Finset.univ (Finset.mem_univ _)
    rw [Finset.card_insert_of_notMem h0] at h1
    have := (hne k).card_pos
    rw [ins]; omega
  · by_cases hl : l = k
    · subst hl; rw [ins, Function.update_self]; exact (hJ l).trans (Finset.subset_insert _ _)
    · rw [ins, Function.update_of_ne hl]; exact hJ l
end GroundTheory.Heights₂.Heights.Kleiman.KHCombContract
