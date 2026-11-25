-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.zCoeff_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:02:40.107447+00:00
-- url     : https://prove2.me/submissions/e3fcaef3-d542-41b3-aff8-4e079e6a1846

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_shellSet_eq_cell
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_ord_of_mem_shellSet
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_dShell_eq_iUnion
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_isOpen_shellSet
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_le_of_mem_shellSet
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_finsum_eq_of_hasSum
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_finite_exponents
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_wt_of_mem
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_integrableOn_dShell
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_GLDoubling_pairwise_disjoint_cell
import Theorems.Thm_GlobalTheory_IwahoriInj_Inj_trans
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_SBUniform_exists_bound_period
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
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
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution {ϖ : kˣ} (hϖ : IsUnif ϖ) {ν : kˣ →* ℂˣ} (hν : IsUnram ν) (d : ℕ) {n : ℕ}
    {φ : Matrix (Fin n) (Fin n) k → ℂ} (hφ : φ ∈ SB _) (m : ℤ) :
    zCoeff n d ϖ ν φ m = cst d ϖ ν ^ m * Jm n φ m := by
  obtain ⟨N, M, hN, -⟩ := GlobalTheory.SBUniform.exists_bound_period k (Fin n) φ hφ
  have hsh : ∀ e : {e : Fin n → ℤ // Antitone e ∧ ∑ i, e i = m},
      shell (haarVol (KO k (Fin n))) ϖ ν ((d : ℂ) / 2) φ e.1 =
        cst d ϖ ν ^ m * ∫ g in shellSet ϖ e.1, φ g.val ∂haarVol (KO k (Fin n)) := fun e => by
    rw [shell, ← integral_const_mul]
    refine setIntegral_congr_fun (isOpen_shellSet ϖ e.1).measurableSet fun g hg => ?_
    have h := wt_of_mem hϖ hν d (g := g) (m := m) ((ord_of_mem_shellSet hϖ hg).trans e.2.2)
    show _ = cst d ϖ ν ^ m * φ g.val
    rw [← h, wt]; ring
  have hdis : Pairwise (Function.onFun Disjoint
      fun e : {e : Fin n → ℤ // Antitone e ∧ ∑ i, e i = m} => shellSet ϖ e.1) := fun a b hab => by
    have h := GlobalTheory.GLDoubling.pairwise_disjoint_cell (N := n) hϖ (i := ⟨a.1, a.2.1⟩) (j := ⟨b.1, b.2.1⟩)
      fun h => hab (Subtype.ext (Subtype.mk.inj h))
    simpa only [Function.onFun, shellSet_eq_cell] using h
  have hint := integrableOn_dShell hφ m
  rw [dShell_eq_iUnion hϖ] at hint
  have hsum := hasSum_integral_iUnion
    (s := fun e : {e : Fin n → ℤ // Antitone e ∧ ∑ i, e i = m} => shellSet ϖ e.1)
    (fun e => (isOpen_shellSet ϖ e.1).measurableSet) hdis hint
  rw [← dShell_eq_iUnion hϖ] at hsum
  have hfin : {e : {e : Fin n → ℤ // Antitone e ∧ ∑ i, e i = m} | ∀ i, -(N : ℤ) ≤ e.1 i}.Finite :=
    ((finite_exponents n (-(N : ℤ)) m).preimage Subtype.val_injective.injOn).subset fun e he => ⟨e.2.2, he⟩
  rw [zCoeff, finsum_congr hsh]
  refine finsum_eq_of_hasSum (hsum.mul_left (cst d ϖ ν ^ m)) hfin fun e he => ?_
  rw [setIntegral_eq_zero_of_forall_eq_zero, mul_zero]
  intro g hg
  by_contra h
  exact he (le_of_mem_shellSet hϖ hg (hN _ h))
end PositivityTheory.ThK.SplitLoc.Unr
