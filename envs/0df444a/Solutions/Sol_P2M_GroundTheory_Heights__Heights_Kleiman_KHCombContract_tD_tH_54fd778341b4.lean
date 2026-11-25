-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_tD_tH_54fd778341b4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:43:06.525794+00:00
-- url     : https://prove2.me/submissions/82a0083a-6d3d-4d45-9407-b57645beeb4c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombContractSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHCombContract
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_faceSign_mul_self_ffdb5f14e040
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_sign_lt_fe63e90e9641
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_sign_gt_862abbabeb9e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_sign_eq_e4cb17e22052
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_sigma_ins_74b9079c2014
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_rem_ins_self_71e833acec92
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_ins_rem_self_60d6f81c0084
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_rem_ins_comm_a1e519b9ef81
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_mem_rem_iff_0c3da7a87a38

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
theorem _root_.solution (k : K) (i₀ : ι k) (F : (∀ k, Finset (ι k)) → S) (hF : ∀ T, (∃ l, T l = ∅) → F T = 0)
    (T : ∀ k, Finset (ι k)) (hT : ∀ l, (T l).Nonempty) :
    tD (tH k i₀ F) T + tH k i₀ (tD F) T = F T := by
  by_cases h0 : i₀ ∈ T k
  · have hH : tH k i₀ (tD F) T = 0 := if_pos h0
    rw [hH, add_zero, tD, Finset.sum_eq_single_of_mem (⟨k, i₀⟩ : Σ k, ι k) (by simp [h0])]
    · have hn : i₀ ∉ rem T k i₀ k := by simp [mem_rem_iff]
      rw [tH, if_neg hn, ins_rem_self T k i₀ h0, smul_smul, faceSign_mul_self, one_smul]
    · rintro ⟨l, i⟩ - hne
      have hm : i₀ ∈ rem T l i k := (mem_rem_iff T k i₀ l i).mpr ⟨h0, hne⟩
      rw [tH, if_pos hm, smul_zero]
  · have hkne := hT k
    have hH : tH k i₀ (tD F) T = KH.faceSign (ins k i₀ T) k i₀ • tD F (ins k i₀ T) := if_neg h0
    have hD : tD F (ins k i₀ T) = ∑ p ∈ Finset.univ.sigma (ins k i₀ T),
        KH.faceSign (ins k i₀ T) p.1 p.2 • F (rem (ins k i₀ T) p.1 p.2) := rfl
    rw [hH, hD, sigma_ins,
      Finset.sum_insert (by simp [h0]), rem_ins_self T k i₀ h0, smul_add, smul_smul, faceSign_mul_self, one_smul]
    have key : tD (tH k i₀ F) T + KH.faceSign (ins k i₀ T) k i₀ •
        ∑ p ∈ Finset.univ.sigma T, KH.faceSign (ins k i₀ T) p.1 p.2 • F (rem (ins k i₀ T) p.1 p.2) = 0 := by
      rw [tD, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun p hp => ?_
      obtain ⟨l, i⟩ := p
      have hi : i ∈ T l := (Finset.mem_sigma.mp hp).2
      have hn : i₀ ∉ rem T l i k := fun hm => h0 ((mem_rem_iff T k i₀ l i).mp hm).1
      rw [tH, if_neg hn, rem_ins_comm T k i₀ l i hi h0, smul_smul, smul_smul, ← add_smul]
      by_cases hz : F (ins k i₀ (rem T l i)) = 0
      · rw [hz, smul_zero]
      have hne : ∀ l', (ins k i₀ (rem T l i) l').Nonempty := by
        intro l'
        by_contra hc
        exact hz (hF _ ⟨l', Finset.not_nonempty_iff_eq_empty.mp hc⟩)
      rcases lt_trichotomy l k with hlk | rfl | hkl
      · have hcard : 2 ≤ (T l).card := by
          have h1 := (hne l).card_pos
          rw [ins, Function.update_of_ne hlk.ne, rem, Function.update_self, Finset.card_erase_of_mem hi] at h1
          omega
        obtain ⟨h1, h2⟩ := sign_lt T k i₀ l i hlk hi hcard
        rw [h1, h2, show KH.faceSign T l i * -KH.faceSign (ins k i₀ T) k i₀ +
          KH.faceSign (ins k i₀ T) k i₀ * KH.faceSign T l i = 0 by ring, zero_smul]
      · rw [sign_eq T l i₀ i hi h0, neg_add_cancel, zero_smul]
      · obtain ⟨h1, h2⟩ := sign_gt T k i₀ l i hkl h0 hkne
        rw [h1, h2, show KH.faceSign T l i * KH.faceSign (ins k i₀ T) k i₀ +
          KH.faceSign (ins k i₀ T) k i₀ * -KH.faceSign T l i = 0 by ring, zero_smul]
    rw [add_left_comm, key, add_zero]
end GroundTheory.Heights₂.Heights.Kleiman.KHCombContract
