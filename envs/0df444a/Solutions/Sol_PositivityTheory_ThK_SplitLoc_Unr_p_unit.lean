-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.p_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:41:48.983429+00:00
-- url     : https://prove2.me/submissions/9e592e8b-24f3-4b5d-a5c3-3e4052ef7733

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_zetaUnr_indicator
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_int_mul
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_indicator_int_mul
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_upperProjection_integral
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_pUnr_eq
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_upperProjection_inverse_transpose_right_inverse
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_SplitFlip_apow_of_valuation_eq_one
import Theorems.Thm_GlobalTheory_SplitFlip_invT_mem_KO
import Theorems.Thm_GlobalTheory_SplitFlip_valuation_gdet_of_mem_KO
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
  [MeasurableSpace k] [BorelSpace k] {a a' : ℕ} {ϖ : kˣ} {α β ν : kˣ →* ℂˣ}
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution (hS : HidaSetting a a' ϖ α β ν) (hν : IsUnram ν) (hβ : IsUnram β) :
    ∀ h ∈ KO k (Fin (a + a')), pUnr a a' ϖ ν β (Set.indicator {X : Matrix (Fin a) (Fin (a + a')) k | ∀ i j, X i j ∈ 𝒪[k]} 1) h = 1 := by
  intro h hh
  have hv := valuation_gdet_of_mem_KO hh
  have hK := (mem_KO_iff h).1 hh
  have hK' := (mem_KO_iff (invT h)).1 (invT_mem_KO hh)
  have e : (fun g : Matrix (Fin a) (Fin a) k =>
      Set.indicator {X : Matrix (Fin a) (Fin (a + a')) k | ∀ i j, X i j ∈ 𝒪[k]} (1 : Matrix (Fin a) (Fin (a + a')) k → ℂ) (g * (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (invT h).val))) =
      Set.indicator {X : Matrix (Fin a) (Fin a) k | ∀ i j, X i j ∈ 𝒪[k]} (1 : Matrix (Fin a) (Fin a) k → ℂ) := by
    funext g
    exact indicator_int_mul (int_mul (upperProjection_integral _) hK'.1) (int_mul (fun i j => hK.1 j i) (fun i j => upperProjection_integral _ j i))
      (upperProjection_inverse_transpose_right_inverse h) g
  rw [pUnr_eq, e, zetaUnr_indicator hS.unif hν, hβ _ hv, apow_of_valuation_eq_one hv]
  simp
end PositivityTheory.ThK.SplitLoc.Unr
