-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_contract_cocycle_0f3cdad47278
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:44:50.647655+00:00
-- url     : https://prove2.me/submissions/fb45226c-76f1-4856-aa5d-6fe43b7baf05

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombCyclicSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombContractSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHCombCyclic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_combD_apply_6bfad6589386
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_cell_ext_28ea0425c440
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_faceOK_congr_1857042b9c83
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_not_faceOK_of_card_one_ac09a1e47140
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_faceSign_update_one_770635500fd3
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
theorem _root_.solution (J : ∀ k, Finset (ι k)) (n : ℕ) (k : K) (i₀ : ι k) (hJ : J k = ∅)
    (φ g : CombC S J n) (hφ : combD S J n φ = 0)
    (hg1 : ∀ I : CombCell ι J n, (I.1.1 k).card = 1 →
      ∃ I' : CombCell ι J n, I'.1.1 k = {i₀} ∧ (∀ l, l ≠ k → I'.1.1 l = I.1.1 l) ∧ g I = φ I')
    (hg0 : ∀ I : CombCell ι J n, (I.1.1 k).card ≠ 1 → g I = 0) :
    combD S J n g = 0 := by
  funext I
  rw [Pi.zero_apply, combD_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  have hz : ∀ l, ∀ i ∈ I.1.1 l, ((Function.update I.1.1 l ((I.1.1 l).erase i)) k).card ≠ 1 →
      (if h : FaceOK J n (Function.update I.1.1 l ((I.1.1 l).erase i)) then
        (KH.faceSign I.1.1 l i : ℤ) • g ⟨⟨_, h.1⟩, h.2⟩ else 0) = 0 := by
    intro l i _ hne
    split_ifs with h
    · rw [hg0 ⟨⟨_, h.1⟩, h.2⟩ hne, smul_zero]
    · rfl
  by_cases h1 : (I.1.1 k).card = 1
  · have hOK : FaceOK J (n + 1) (Function.update I.1.1 k {i₀}) :=
      (faceOK_congr hJ (by rw [Function.update_self, Finset.card_singleton, h1])
        (fun m hm => (Function.update_of_ne hm _ _).symm)).mp ⟨I.1.2, I.2⟩
    obtain ⟨I', hI'⟩ : ∃ I' : CombCell ι J (n + 1), I'.1.1 = Function.update I.1.1 k {i₀} :=
      ⟨⟨⟨_, hOK.1⟩, hOK.2⟩, rfl⟩
    have hφI' := congrFun hφ I'
    rw [Pi.zero_apply, combD_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at hφI'
    refine Eq.trans ?_ hφI'
    have hI'k : (I'.1.1 k).card = 1 := by rw [hI', Function.update_self, Finset.card_singleton]
    congr 1
    · rw [Finset.sum_eq_zero fun i hi => dif_neg (not_faceOK_of_card_one _ k hi h1),
        Finset.sum_eq_zero fun i hi => dif_neg (not_faceOK_of_card_one _ k hi hI'k)]
    refine Finset.sum_congr rfl fun l hlm => ?_
    have hl : l ≠ k := Finset.ne_of_mem_erase hlm
    have hset : I.1.1 l = I'.1.1 l := by rw [hI', Function.update_of_ne hl]
    refine Finset.sum_congr hset fun i hi => ?_
    have hF' : Function.update I'.1.1 l ((I'.1.1 l).erase i) =
        Function.update (Function.update I.1.1 l ((I.1.1 l).erase i)) k {i₀} := by
      rw [← hset, hI', Function.update_comm (Ne.symm hl)]
    have hFk : ((Function.update I.1.1 l ((I.1.1 l).erase i)) k).card = 1 := by
      rw [Function.update_of_ne (Ne.symm hl), h1]
    have hiff : FaceOK J n (Function.update I.1.1 l ((I.1.1 l).erase i)) ↔
        FaceOK J n (Function.update I'.1.1 l ((I'.1.1 l).erase i)) := by
      rw [hF']
      exact faceOK_congr hJ (by rw [Function.update_self, Finset.card_singleton, hFk])
        (fun m hm => (Function.update_of_ne hm _ _).symm)
    have hsign : KH.faceSign I'.1.1 l i = KH.faceSign I.1.1 l i := by
      rw [hI']
      exact faceSign_update_one I.1.1 hl i {i₀} h1 (Finset.card_singleton i₀)
    by_cases hc : FaceOK J n (Function.update I.1.1 l ((I.1.1 l).erase i))
    · rw [dif_pos hc, dif_pos (hiff.mp hc), hsign]
      obtain ⟨I'', hk'', ho'', hgI⟩ := hg1 ⟨⟨_, hc.1⟩, hc.2⟩ hFk
      rw [hgI]
      congr 1
      refine congrArg φ (cell_ext ?_)
      show I''.1.1 = Function.update I'.1.1 l ((I'.1.1 l).erase i)
      rw [hF', Function.eq_update_iff]
      exact ⟨hk'', fun m hm => ho'' m hm⟩
    · rw [dif_neg hc, dif_neg (fun h => hc (hiff.mpr h))]
  · by_cases h2 : (I.1.1 k).card = 2
    · rw [Finset.sum_eq_zero fun l hlm => Finset.sum_eq_zero fun i hi => hz l i hi (by
        rw [Function.update_of_ne (Ne.symm (Finset.ne_of_mem_erase hlm)), h2]; omega), add_zero]
      have hrep : ∀ i ∈ I.1.1 k, ∀ Ii : CombCell ι J n, Ii.1.1 k = {i₀} →
          (∀ m, m ≠ k → Ii.1.1 m = Function.update I.1.1 k ((I.1.1 k).erase i) m) →
          Ii.1.1 = Function.update I.1.1 k {i₀} := fun i _ Ii hk ho => by
        rw [Function.eq_update_iff]
        exact ⟨hk, fun m hm => (ho m hm).trans (Function.update_of_ne hm _ _)⟩
      have hcard : ∀ i ∈ I.1.1 k, ((Function.update I.1.1 k ((I.1.1 k).erase i)) k).card = 1 := fun i hi => by
        rw [Function.update_self, Finset.card_erase_of_mem hi, h2]
      refine block_pair J n g I k hJ h2 fun i hi j hj hi' hj' => ?_
      obtain ⟨Ii, hki, hoi, hgi⟩ := hg1 ⟨⟨_, hi'.1⟩, hi'.2⟩ (hcard i hi)
      obtain ⟨Ij, hkj, hoj, hgj⟩ := hg1 ⟨⟨_, hj'.1⟩, hj'.2⟩ (hcard j hj)
      rw [hgi, hgj]
      exact congrArg φ (cell_ext ((hrep i hi Ii hki hoi).trans (hrep j hj Ij hkj hoj).symm))
    · rw [Finset.sum_eq_zero fun i hi => hz k i hi (by
          rw [Function.update_self, Finset.card_erase_of_mem hi]
          have := Finset.card_pos.mpr ⟨i, hi⟩
          omega),
        Finset.sum_eq_zero fun l hlm => Finset.sum_eq_zero fun i hi => hz l i hi (by
          rw [Function.update_of_ne (Ne.symm (Finset.ne_of_mem_erase hlm))]; exact h1), add_zero]
end GroundTheory.Heights₂.Heights.Kleiman.KHCombCyclic
