-- Prove2me | solution 1 for QEC.Coding.CSSGibbs.rowProbability_selection_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:40:42.106193+00:00
-- url     : https://prove2.me/submissions/939bf834-9ee1-45ae-9d4e-993838482ead

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Gibbs
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
import Theorems.Thm_QEC_Coding_CSSGibbs_rowProbability_nonneg
import Theorems.Thm_QEC_Coding_CSSGibbs_sum_rowProbability


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.CSSGibbs
open Classical Semantics
open scoped BigOperators
variable {ι κP κQ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κP] [Fintype κQ] [DecidableEq κP] [DecidableEq κQ]
variable (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
  (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
  (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
attribute [local instance] QEC.Coding.CSSGibbs._p2m_local_instance_807a85e857_19
attribute [local instance] QEC.Coding.CSSGibbs._p2m_local_instance_807a85e857_20
namespace QEC.Coding.CSSGibbs
theorem _root_.solution (t : ℝ) (A : Finset (LinearMap.range P)) :
    0 ≤ ∑ u ∈ A, rowProbability P t u ∧ (∑ u ∈ A, rowProbability P t u) ≤ 1 := by
  refine ⟨Finset.sum_nonneg (fun u _ => rowProbability_nonneg P t u), ?_⟩
  calc
    _ ≤ ∑ u, rowProbability P t u :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
        (fun u _ _ => rowProbability_nonneg P t u)
    _ = 1 := sum_rowProbability P t
end QEC.Coding.CSSGibbs
