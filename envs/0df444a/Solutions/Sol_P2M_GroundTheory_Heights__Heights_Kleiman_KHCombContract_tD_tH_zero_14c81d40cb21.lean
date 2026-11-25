-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_tD_tH_zero_14c81d40cb21
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:07:14.379863+00:00
-- url     : https://prove2.me/submissions/a554c6b4-f57c-44ff-abd2-58f1b0ddb8b7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombContractSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHCombContract
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_ext_of_empty_fe169bb191f2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_cell_card_eq_one_of_degree_zero_fbc2cedc2648

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
theorem _root_.solution (J : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (φ : CombC S J 0) (I : CombCell ι J 0) :
    tD (tH k i₀ (ext J 0 φ)) I.1.1 = tD (corr J k i₀ 0 φ) I.1.1 := by
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨l, i⟩ := p
  have hi : i ∈ I.1.1 l := (Finset.mem_sigma.mp hp).2
  have hemp : (I.1.1 l).erase i = ∅ := by
    rw [← Finset.card_eq_zero, Finset.card_erase_of_mem hi, cell_card_eq_one_of_degree_zero I.1 l]
  congr 1
  rw [corr]
  split_ifs with hT
  · rfl
  · have hl : l ≠ k := by
      rintro rfl
      exact hT (by rw [rem, Function.update_self, hemp])
    rw [tH]
    split_ifs
    · rfl
    · rw [ext_of_empty J 0 φ _ ⟨l, by rw [ins, Function.update_of_ne hl, rem, Function.update_self, hemp]⟩,
        smul_zero]
end GroundTheory.Heights₂.Heights.Kleiman.KHCombContract
