-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.summable_Jm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:57:06.118671+00:00
-- url     : https://prove2.me/submissions/81a811da-c543-41af-9723-c9959f9b8755

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_Jm_mul_left
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_exists_normal
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_Jm_hnf
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_summable_antidiag_of_growth
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_SplitFlip_comp_mul_mem_SB
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
  [MeasurableSpace k] [BorelSpace k]
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution {ϖ : kˣ} (hϖ : IsUnif ϖ) {n : ℕ} {φ : Matrix (Fin n) (Fin n) k → ℂ} (hφ : φ ∈ SB _) {r : ℝ}
    (hr : 0 < r) (hrq : ∀ i : Fin n, r * (resCard k : ℝ) ^ (n - 1 - (i : ℕ)) < 1) :
    Summable fun m : ℤ => r ^ m * ‖Jm n φ m‖ := by
  obtain ⟨N, M, hs, hp⟩ := exists_normal hϖ hφ
  set g₁ : GL (Fin n) k := scal n (ϖ ^ N)⁻¹ with hg₁
  have h0 : (fun x => φ (g₁.val * x)) ∈ SB _ := by
    simpa using comp_mul_mem_SB g₁ 1 hφ
  obtain ⟨T, hT, hneg, hnat⟩ := Jm_hnf hϖ h0 hs M hp
  have hq : (1 : ℝ) ≤ resCard k := by
    have : 1 < resCard k := Finite.one_lt_card
    exact_mod_cast this.le
  have h1 := summable_antidiag_of_growth (fun i : Fin n => (resCard k : ℝ) ^ (n - 1 - (i : ℕ)))
    (fun i => one_le_pow₀ hq) hr.le hrq M T (fun a => by rw [hT a]; push_cast; rfl)
  have h2 : Summable fun m : ℤ => r ^ m * ‖Jm n (fun x => φ (g₁.val * x)) m‖ := by
    refine Summable.of_nat_of_neg_add_one ?_ ?_
    · refine h1.congr fun t => ?_
      rw [hnat t, zpow_natCast]
    · refine summable_zero.congr fun t => ?_
      rw [hneg _ (by omega), norm_zero, mul_zero]
  set e : ℤ := ord k (gdet g₁)
  rw [← (Equiv.addRight e).summable_iff]
  refine (h2.mul_left (r ^ e)).congr fun m => ?_
  simp only [Function.comp_apply, Equiv.coe_addRight]
  rw [Jm_mul_left, zpow_add₀ hr.ne']
  ring
end PositivityTheory.ThK.SplitLoc.Unr
