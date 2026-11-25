-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_det_gram_sumElim_66edcb621772
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:34:37.640743+00:00
-- url     : https://prove2.me/submissions/25d416cb-6227-435f-af17-bbece7453805

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (a : m → V) (b q : n → V) (C : Matrix m n ℂ) (hq : ∀ j, q j = b j - ∑ i, C i j • a i)
    (horth : ∀ i j, inner ℂ (a i) (q j) = 0) :
    det (gram ℂ (Sum.elim a b)) = det (gram ℂ a) * det (gram ℂ q) := by
  let T : Matrix (m ⊕ n) (m ⊕ n) ℂ := fromBlocks 1 (-C) 0 1
  have h1 : Sum.elim a q = fun k ↦ ∑ l, T l k • Sum.elim a b l := by
    funext k
    rcases k with i | j
    · simp [T, Fintype.sum_sum_type, one_apply, ite_smul]
    · simp only [T, Fintype.sum_sum_type, Sum.elim_inr, Sum.elim_inl, fromBlocks_apply₁₂,
        fromBlocks_apply₂₂, one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, hq j]
      simp only [Matrix.neg_apply, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]
      exact add_comm _ _
  have h2 : det T = 1 := by simp [T]
  have h3 : gram ℂ (Sum.elim a q) = fromBlocks (gram ℂ a) 0 0 (gram ℂ q) := by
    ext k l
    rcases k with i | j <;> rcases l with i' | j'
    · rfl
    · simp [gram_apply, horth]
    · simp [gram_apply, inner_eq_zero_symm.mp (horth i' j)]
    · rfl
  calc det (gram ℂ (Sum.elim a b)) = det (gram ℂ (Sum.elim a q)) := by
        rw [h1, gram_comb, det_mul, det_mul, det_conjTranspose, h2, star_one, one_mul, mul_one]
    _ = det (gram ℂ a) * det (gram ℂ q) := by rw [h3, det_fromBlocks_zero₂₁]
end GroundTheory.Heights₂.Heights
