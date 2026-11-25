-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_cond_of_ins_e966a7d8f2f2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:12.451294+00:00
-- url     : https://prove2.me/submissions/057fd3c1-40b5-49b3-86fa-14cd82fa2914

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
theorem _root_.solution (J : ∀ k, Finset (ι k)) (d : ℕ) (k : K) (i₀ : ι k) (hJ0 : i₀ ∉ J k) (T : ∀ k, Finset (ι k))
    (h0 : i₀ ∉ T k) (hk : (T k).Nonempty)
    (h : ((∀ l, (ins k i₀ T l).Nonempty) ∧ ∑ l, ((ins k i₀ T l).card - 1) = d + 1) ∧ ∀ l, J l ⊆ ins k i₀ T l) :
    ((∀ l, (T l).Nonempty) ∧ ∑ l, ((T l).card - 1) = d) ∧ ∀ l, J l ⊆ T l := by
  obtain ⟨⟨hne, hsum⟩, hJ⟩ := h
  refine ⟨⟨fun l => ?_, ?_⟩, fun l => ?_⟩
  · by_cases hl : l = k
    · subst hl; exact hk
    · have := hne l; rwa [ins, Function.update_of_ne hl] at this
  · have h1 := sum_card_update_of_mem T k (insert i₀ (T k)) Finset.univ (Finset.mem_univ _)
    rw [Finset.card_insert_of_notMem h0] at h1
    have := hk.card_pos
    rw [ins] at hsum; omega
  · by_cases hl : l = k
    · subst hl
      have := hJ l
      rw [ins, Function.update_self] at this
      exact (Finset.subset_insert_iff_of_notMem hJ0).mp this
    · have := hJ l; rwa [ins, Function.update_of_ne hl] at this
end GroundTheory.Heights₂.Heights.Kleiman.KHCombContract
