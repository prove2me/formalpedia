-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.sum_comp_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:01:58.373046+00:00
-- url     : https://prove2.me/submissions/ff135d9e-086e-4714-81cc-f756d1bfbe41

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
variable [MeasurableSpace k] [BorelSpace k]
open GlobalTheory.SatakeBound
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution {G H : Type*} [AddGroup G] [AddGroup H] [Fintype G] [Fintype H] (π : G →+ H)
    (hπ : Function.Surjective π) {r : ℕ} (hr : Nat.card G = r * Nat.card H) (F : H → ℂ) :
    ∑ c, F (π c) = r * ∑ d, F d := by
  classical
  have h1 : ∀ d, (Finset.univ.filter fun c => π c = d).card = (Finset.univ.filter fun c => π c = 0).card := fun d =>
    AddMonoidHom.card_fiber_eq_of_mem_range π (hπ d) (hπ 0)
  have h2 := Finset.card_eq_sum_card_fiberwise (f := π) (s := Finset.univ) (t := Finset.univ)
    fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)
  simp only [h1, Finset.sum_const, smul_eq_mul, Finset.card_univ, ← Nat.card_eq_fintype_card] at h2
  have h3 : (Finset.univ.filter fun c => π c = 0).card = r :=
    Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := H)) (by rw [← h2, hr, mul_comm])
  rw [← Finset.sum_fiberwise' Finset.univ π F, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_const, h1, h3, nsmul_eq_mul]
end PositivityTheory.ThK.SplitLoc.Unr
