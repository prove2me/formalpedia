-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_corr_zero_a06d0001c939
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:14.277464+00:00
-- url     : https://prove2.me/submissions/df4c41f3-51b8-4b77-bc66-c580c36b029c

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
theorem _root_.solution (J : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (hJ0 : i₀ ∉ J k) (d : ℕ) (φ : CombC S J d)
    (I : CombCell ι J d) (h : ¬ (J k = ∅ ∧ (I.1.1 k).card = 1)) :
    tD (corr J k i₀ d φ) I.1.1 = 0 := by
  refine Finset.sum_eq_zero fun p hp => ?_
  obtain ⟨l, j⟩ := p
  have hj : j ∈ I.1.1 l := (Finset.mem_sigma.mp hp).2
  rw [corr]
  split_ifs with hT
  swap
  · exact smul_zero _
  have hl : l = k := by
    by_contra hl
    rw [rem, Function.update_of_ne (Ne.symm hl)] at hT
    exact (I.1.2.1 k).ne_empty hT
  subst hl
  have hT' : (I.1.1 l).erase j = ∅ := by rw [rem, Function.update_self] at hT; exact hT
  have h1 : (I.1.1 l).card = 1 := by
    have := Finset.card_erase_of_mem hj
    rw [hT', Finset.card_empty] at this
    have := (I.1.2.1 l).card_pos
    omega
  have hJne : ¬ J l = ∅ := fun e => h ⟨e, h1⟩
  rw [tH, if_neg (by rw [hT]; exact Finset.notMem_empty _), ext, dif_neg]
  · simp
  rintro ⟨-, hJ⟩
  have hsub := hJ l
  rw [ins, Function.update_self, hT, Finset.insert_empty] at hsub
  rcases Finset.subset_singleton_iff.mp hsub with e | e
  · exact hJne e
  · exact hJ0 (e ▸ Finset.mem_singleton_self _)
end GroundTheory.Heights₂.Heights.Kleiman.KHCombContract
