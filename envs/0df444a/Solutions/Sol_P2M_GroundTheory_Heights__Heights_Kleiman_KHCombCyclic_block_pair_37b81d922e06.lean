-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_block_pair_37b81d922e06
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:07:05.067329+00:00
-- url     : https://prove2.me/submissions/1d958a69-2b67-41a1-b5e8-ea333a3cf65f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombCyclicSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombContractSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHCombCyclic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_faceOK_congr_1857042b9c83
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_faceSign_pair_b9b696b63fc2

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
theorem _root_.solution (J : ∀ k, Finset (ι k)) (n : ℕ) (f : CombC S J n) (I : CombCell ι J (n + 1)) (k : K)
    (hJ : J k = ∅) (h2 : (I.1.1 k).card = 2)
    (hf : ∀ i ∈ I.1.1 k, ∀ j ∈ I.1.1 k,
      ∀ (hi : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase i)))
        (hj : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase j))),
      f ⟨⟨_, hi.1⟩, hi.2⟩ = f ⟨⟨_, hj.1⟩, hj.2⟩) :
    ∑ i ∈ I.1.1 k, (if h : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase i)) then
        (KH.faceSign I.1.1 k i : ℤ) • f ⟨⟨_, h.1⟩, h.2⟩ else 0) = 0 := by
  obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp h2
  have ha : a ∈ I.1.1 k := by rw [he]; simp
  have hb : b ∈ I.1.1 k := by rw [he]; simp
  have hiff : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase a)) ↔
      FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase b)) :=
    faceOK_congr hJ (by rw [Function.update_self, Function.update_self, Finset.card_erase_of_mem ha,
      Finset.card_erase_of_mem hb]) (fun m hm => by rw [Function.update_of_ne hm, Function.update_of_ne hm])
  let t : ι k → S := fun i => if h : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase i)) then
      (KH.faceSign I.1.1 k i : ℤ) • f ⟨⟨_, h.1⟩, h.2⟩ else 0
  show ∑ i ∈ I.1.1 k, t i = 0
  rw [he, Finset.sum_pair hab]
  by_cases hOK : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase a))
  · have hOK' := hiff.mp hOK
    simp only [t]
    rw [dif_pos hOK, dif_pos hOK', hf b hb a ha hOK' hOK]
    rcases lt_or_gt_of_ne hab with h | h
    · rw [faceSign_pair I.1.1 k h he, neg_smul, add_neg_cancel]
    · rw [faceSign_pair I.1.1 k h (he.trans (Finset.pair_comm a b)), neg_smul, neg_add_cancel]
  · simp only [t]
    rw [dif_neg hOK, dif_neg (fun h => hOK (hiff.mpr h)), add_zero]
end GroundTheory.Heights₂.Heights.Kleiman.KHCombCyclic
