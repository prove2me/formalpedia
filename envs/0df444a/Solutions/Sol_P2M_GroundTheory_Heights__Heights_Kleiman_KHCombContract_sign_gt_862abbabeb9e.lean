-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_sign_gt_862abbabeb9e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:29:19.036627+00:00
-- url     : https://prove2.me/submissions/7e0b1e44-4216-47d0-9376-8ea471544af5

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
theorem _root_.solution (T : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (l : K) (i : ι l) (hkl : k < l)
    (hk0 : i₀ ∉ T k) (hkne : (T k).Nonempty) :
    KH.faceSign (ins k i₀ (rem T l i)) k i₀ = KH.faceSign (ins k i₀ T) k i₀ ∧
      KH.faceSign (ins k i₀ T) l i = - KH.faceSign T l i := by
  have hne : l ≠ k := hkl.ne'
  constructor
  · have hl : l ∉ Finset.univ.filter (· < k) := by simp [hkl.le]
    have hk : k ∉ Finset.univ.filter (· < k) := by simp
    rw [faceSign_eq, faceSign_eq, ins, ins, rem, Function.update_self, Function.update_self,
      Function.update_of_ne hne.symm, sum_card_update_of_notMem _ _ _ _ hk, sum_card_update_of_notMem _ _ _ _ hk,
      sum_card_update_of_notMem _ _ _ _ hl]
  · have hmem : k ∈ Finset.univ.filter (· < l) := by simp [hkl]
    have h1 := sum_card_update_of_mem T k (insert i₀ (T k)) _ hmem
    rw [Finset.card_insert_of_notMem hk0] at h1
    have hpos := hkne.card_pos
    rw [faceSign_eq, faceSign_eq, ins, Function.update_of_ne hne]
    have h2 : ∑ x ∈ Finset.univ.filter (· < l), ((Function.update T k (insert i₀ (T k)) x).card - 1) =
        (∑ x ∈ Finset.univ.filter (· < l), ((T x).card - 1)) + 1 := by omega
    rw [h2, pow_succ]; ring
end GroundTheory.Heights₂.Heights.Kleiman.KHCombContract
