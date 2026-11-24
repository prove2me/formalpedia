-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.ord_gdet_of_mem_coset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:16:54.931143+00:00
-- url     : https://prove2.me/submissions/ab8509ca-8f55-4d1a-8cc1-d3a7817be54d

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
import Theorems.Thm_GlobalTheory_SatakeBound_val_hermGL
import Theorems.Thm_GlobalTheory_SmGL_ord_eq_one
import Theorems.Thm_GlobalTheory_SplitFlip_IsUnif_irreducible
import Theorems.Thm_GlobalTheory_SplitFlip_gdet_mul
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
variable [MeasurableSpace k] [BorelSpace k]
open GlobalTheory.SatakeBound
omit [MeasurableSpace k] [BorelSpace k]
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution {ϖ : kˣ} (hϖ : IsUnif ϖ) {n : ℕ} {a : Fin n → ℕ} {c : HermIdx _ a} {g : GL (Fin n) k}
    (hg : (hermGL hϖ.irreducible a c)⁻¹ * g ∈ KO k (Fin n)) : ord k (gdet g) = (∑ i, a i : ℕ) := by
  have h1 : ∀ m : ℕ, ord k (ϖ ^ m) = m := fun m => by
    induction m with
    | zero => exact ord_eq_zero (by simp)
    | succ m ih => rw [pow_succ, ord_mul, ih, ord_eq_one hϖ]; simp
  have h2 : gdet (hermGL hϖ.irreducible a c) = ϖ ^ ∑ i, a i := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, val_hermGL, ← RingHom.map_det, det_hermMat, map_pow,
      Units.val_pow_eq_pow_val]
    rfl
  rw [← mul_inv_cancel_left (hermGL hϖ.irreducible a c) g, gdet_mul, ord_mul, h2, h1,
    ord_eq_zero (valuation_gdet_of_mem_KO hg), add_zero]
end PositivityTheory.ThK.SplitLoc.Unr
