-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_singOne_cocycle_ebe7863fb360
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:44:51.643057+00:00
-- url     : https://prove2.me/submissions/6d3890ea-176c-4e19-a85f-e07ec3a08794

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombCyclicSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombContractSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHCombCyclic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_combD_apply_6bfad6589386
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_block_pair_37b81d922e06

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
open GroundTheory.Heights₂.Heights.Kleiman.KHCombCyclic
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
open Classical
namespace GroundTheory.Heights₂.Heights.Kleiman.KHCombCyclic
theorem _root_.solution (J : ∀ k, Finset (ι k)) (n : ℕ) (hJ : ∀ k, J k = ∅ ∨ J k = Finset.univ) :
    combD S J n (singOne S J n) = 0 := by
  funext I
  rw [combD_apply, Pi.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases hJ k with hk | hk
  · by_cases hc : (I.1.1 k).card = 2 ∧ ∀ m, m ≠ k → J m = ∅ → (I.1.1 m).card = 1
    · have key : ∀ i ∈ I.1.1 k, ∀ hi' : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase i)),
          singOne S J n ⟨⟨_, hi'.1⟩, hi'.2⟩ = 1 := by
        intro i hi hi'
        simp only [singOne]
        rw [if_pos]
        intro m hm
        by_cases hmk : m = k
        · rw [hmk, Function.update_self, Finset.card_erase_of_mem hi, hc.1]
        · rw [Function.update_of_ne hmk]
          exact hc.2 m hmk hm
      refine block_pair J n _ I k hk hc.1 fun i hi j hj hi' hj' => ?_
      rw [key i hi hi', key j hj hj']
    · refine Finset.sum_eq_zero fun i hi => ?_
      split_ifs with h
      · have h0 : singOne S J n ⟨⟨_, h.1⟩, h.2⟩ = 0 := by
          simp only [singOne]
          rw [if_neg]
          intro hall
          apply hc
          have hpos : 0 < (I.1.1 k).card := Finset.card_pos.mpr ⟨i, hi⟩
          have hkk := hall k hk
          rw [Function.update_self, Finset.card_erase_of_mem hi] at hkk
          refine ⟨by omega, fun m hm hJm => ?_⟩
          have := hall m hJm
          rwa [Function.update_of_ne hm] at this
        rw [h0, smul_zero]
      · rfl
  · refine Finset.sum_eq_zero fun i hi => dif_neg fun h => ?_
    have hiJ : i ∈ J k := by rw [hk]; exact Finset.mem_univ i
    have := h.2 k hiJ
    rw [Function.update_self] at this
    exact Finset.notMem_erase i _ this
end GroundTheory.Heights₂.Heights.Kleiman.KHCombCyclic
