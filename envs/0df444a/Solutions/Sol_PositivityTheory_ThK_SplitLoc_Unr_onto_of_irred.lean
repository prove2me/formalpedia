-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.onto_of_irred
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:13:47.704123+00:00
-- url     : https://prove2.me/submissions/f403956e-19d0-4e1e-b413-3d95b0f2deb0

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.SplitLoc PositivityTheory.ThK.SplitLoc.Unr
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SmGL
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution (hI : IndIrred) {a a' : ℕ} {α β : kˣ →* ℂˣ} (hα : ∀ x, ‖(α x : ℂ)‖ = 1)
    (hβ : ∀ x, ‖(β x : ℂ)‖ = 1) {X : Type} [TopologicalSpace X] (p : (X → ℂ) → GL (Fin (a + a')) k → ℂ)
    (hlin : ∀ Φ ∈ SB X, ∀ Φ₁ ∈ SB X, ∀ c : ℂ, p (Φ + c • Φ₁) = p Φ + c • p Φ₁)
    (hin : ∀ Φ ∈ SB X, p Φ ∈ indSp a a' α β)
    (heq : ∀ Φ ∈ SB X, ∀ h₁, ∃ Φ' ∈ SB X, p Φ' = rtr h₁ (p Φ))
    (hne : ∃ Φ ∈ SB X, p Φ ≠ 0) : ∀ F ∈ indSp a a' α β, ∃ Φ ∈ SB X, p Φ = F := by
  have h0 : p 0 = 0 := by
    have := hlin 0 (SB X).zero_mem 0 (SB X).zero_mem 1
    simpa using this
  let N : Submodule ℂ (GL (Fin (a + a')) k → ℂ) :=
    { carrier := {F | ∃ Φ ∈ SB X, p Φ = F}
      add_mem' := by
        rintro _ _ ⟨Φ, hΦ, rfl⟩ ⟨Φ₁, hΦ₁, rfl⟩
        exact ⟨Φ + (1 : ℂ) • Φ₁, (SB X).add_mem hΦ ((SB X).smul_mem _ hΦ₁), by rw [hlin _ hΦ _ hΦ₁, one_smul]⟩
      zero_mem' := ⟨0, (SB X).zero_mem, h0⟩
      smul_mem' := by
        rintro c _ ⟨Φ, hΦ, rfl⟩
        exact ⟨0 + c • Φ, (SB X).add_mem (SB X).zero_mem ((SB X).smul_mem _ hΦ), by
          rw [hlin _ (SB X).zero_mem _ hΦ, h0, zero_add]⟩ }
  have hle : N ≤ indSp a a' α β := by
    rintro _ ⟨Φ, hΦ, rfl⟩
    exact hin Φ hΦ
  have hst : ∀ h₁, ∀ F ∈ N, rtr h₁ F ∈ N := by
    rintro h₁ _ ⟨Φ, hΦ, rfl⟩
    exact heq Φ hΦ h₁
  rcases hI k a a' α β hα hβ N hle hst with h | h
  · obtain ⟨Φ, hΦ, hne⟩ := hne
    have hm : p Φ ∈ N := ⟨Φ, hΦ, rfl⟩
    rw [h] at hm
    exact absurd ((Submodule.mem_bot ℂ).1 hm) hne
  · intro F hF
    rw [← h] at hF
    exact hF
end PositivityTheory.ThK.SplitLoc.Unr
