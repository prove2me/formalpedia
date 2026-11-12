-- Prove2me | solution 1 for QEC.Coding.FixedCoboundaryGibbs.weight_remove
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:58:35.158498+00:00
-- url     : https://prove2.me/submissions/846e4b88-942b-4877-84d6-9ee524df9c92

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_CoboundaryContainment
import Theorems.Thm_QEC_Coding_FixedCoboundaryGibbs_support_remove
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.FixedCoboundaryGibbs
open Classical
open scoped BigOperators
variable {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
attribute [local instance] QEC.Coding.FixedCoboundaryGibbs.imageFintype
namespace QEC.Coding.FixedCoboundaryGibbs
theorem _root_.solution (s τ : Word (ZMod 2) K)
    (h : hammingSupport τ ⊆ hammingSupport s) :
    HammingWeight s = HammingWeight τ + HammingWeight (s+τ) := by
  change (hammingSupport s).card = (hammingSupport τ).card + (hammingSupport (s+τ)).card
  rw [support_remove s τ h]
  exact (Finset.card_sdiff_add_card_eq_card h).symm.trans (Nat.add_comm _ _)
end QEC.Coding.FixedCoboundaryGibbs
