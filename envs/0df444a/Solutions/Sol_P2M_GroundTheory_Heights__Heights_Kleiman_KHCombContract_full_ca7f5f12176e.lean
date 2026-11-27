-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_full_ca7f5f12176e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:02:44.155454+00:00
-- url     : https://prove2.me/submissions/bd167c8e-96f1-439c-aa26-93fb20ffab3f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombContractSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHCombContract
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_hh_zero_cb11064b0460
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_corr_single_955f73d9e620
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_corr_zero_a06d0001c939
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_homotopy_succ_06f320cbc407
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_homotopy_zero_79af76184472

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
theorem _root_.solution : KHCombContract.Statement := by
  intro S _ K _ _ ι _ _ J n k i₀ hJ0 f hf
  suffices H : ∃ g : CombC S J n, f - g ∈ combB S J n ∧ ∀ I, g I = tD (corr J k i₀ n f) I.1.1 by
    obtain ⟨g, hg, hgI⟩ := H
    refine ⟨g, hg, fun I => ⟨fun h => ⟨repl J k i₀ n I h.1 h.2, Function.update_self _ _ _,
      fun l hl => Function.update_of_ne hl _ _, ?_⟩, fun h => ?_⟩⟩
    · rw [hgI, corr_single]
    · rw [hgI, corr_zero J k i₀ hJ0 n f I h]
  cases n with
  | zero =>
    refine ⟨f, ?_, fun I => ?_⟩
    · show f - f ∈ (⊥ : Submodule S (CombC S J 0))
      rw [sub_self]
      exact Submodule.zero_mem _
    · have h := homotopy_zero J k i₀ f I
      rw [hf, hh_zero, Pi.zero_apply, zero_add] at h
      exact h.symm
  | succ m =>
    refine ⟨f - combD S J m (hh J k i₀ m f), ?_, fun I => ?_⟩
    · show _ ∈ LinearMap.range (combD S J m)
      rw [sub_sub_cancel]
      exact LinearMap.mem_range_self _ _
    · have h := homotopy_succ J k i₀ hJ0 m f I
      rw [hf, hh_zero, Pi.zero_apply, add_zero] at h
      rw [Pi.sub_apply, ← h]
      abel
end GroundTheory.Heights₂.Heights.Kleiman.KHCombContract
