-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_mem_rem_iff_0c3da7a87a38
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:06:41.480132+00:00
-- url     : https://prove2.me/submissions/ebab9f87-7245-4cc8-a286-167a46026947

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
theorem _root_.solution (T : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (l : K) (i : ι l) :
    i₀ ∈ rem T l i k ↔ i₀ ∈ T k ∧ (⟨l, i⟩ : Σ k, ι k) ≠ ⟨k, i₀⟩ := by
  by_cases h : l = k
  · subst h
    simp only [rem, Function.update_self, Finset.mem_erase, ne_eq, Sigma.mk.inj_iff, heq_eq_eq, true_and]
    tauto
  · simp only [rem, Function.update_of_ne (Ne.symm h), ne_eq, Sigma.mk.inj_iff, h, false_and, not_false_eq_true,
      and_true]
end GroundTheory.Heights₂.Heights.Kleiman.KHCombContract
