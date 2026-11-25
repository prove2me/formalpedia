-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_sign_eq_e4cb17e22052
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:06:09.102365+00:00
-- url     : https://prove2.me/submissions/04ce56a7-6f0e-41d6-b8aa-16589902ab1c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombContractSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHCombContract
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_sum_card_update_of_notMem_8b37477be765
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_faceSign_eq_ce253517e0b4

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
namespace GroundTheory.Heights₂.Heights.Kleiman.KHCombContract
theorem _root_.solution (T : ∀ k, Finset (ι k)) (k : K) (i₀ i : ι k) (hi : i ∈ T k) (hk0 : i₀ ∉ T k) :
    KH.faceSign T k i * KH.faceSign (ins k i₀ (rem T k i)) k i₀ =
      - (KH.faceSign (ins k i₀ T) k i₀ * KH.faceSign (ins k i₀ T) k i) := by
  have hne : i ≠ i₀ := fun h => hk0 (h ▸ hi)
  have hk : k ∉ Finset.univ.filter (· < k) := by simp
  rw [faceSign_eq, faceSign_eq, faceSign_eq, faceSign_eq, ins, ins, rem, Function.update_self,
    Function.update_self, Function.update_self, sum_card_update_of_notMem _ _ _ _ hk,
    sum_card_update_of_notMem _ _ _ _ hk, sum_card_update_of_notMem _ _ _ _ hk]
  set C := ∑ x ∈ Finset.univ.filter (· < k), ((T x).card - 1)
  have hb : (insert i₀ (T k)).filter (· < i₀) = (T k).filter (· < i₀) := by simp [Finset.filter_insert]
  have hb2 : (insert i₀ ((T k).erase i)).filter (· < i₀) = ((T k).filter (· < i₀)).erase i := by
    simp [Finset.filter_insert, Finset.filter_erase]
  rw [hb, hb2]
  rcases lt_or_gt_of_ne hne with h | h
  · have ha : (insert i₀ (T k)).filter (· < i) = (T k).filter (· < i) := by
      simp [Finset.filter_insert, not_lt.mpr h.le]
    rw [ha]
    have hm : i ∈ (T k).filter (· < i₀) := Finset.mem_filter.mpr ⟨hi, h⟩
    have hc := Finset.card_erase_of_mem hm
    have hp := Finset.card_pos.mpr ⟨i, hm⟩
    have : ((T k).filter (· < i₀)).card = (((T k).filter (· < i₀)).erase i).card + 1 := by omega
    rw [this, pow_succ]; ring
  · have ha : (insert i₀ (T k)).filter (· < i) = insert i₀ ((T k).filter (· < i)) := by
      simp [Finset.filter_insert, h]
    rw [ha, Finset.card_insert_of_notMem (fun hm => hk0 (Finset.mem_filter.mp hm).1)]
    have hm : i ∉ (T k).filter (· < i₀) := fun hm => absurd (Finset.mem_filter.mp hm).2 (not_lt.mpr h.le)
    rw [Finset.erase_eq_of_notMem hm, pow_succ]; ring
end GroundTheory.Heights₂.Heights.Kleiman.KHCombContract
