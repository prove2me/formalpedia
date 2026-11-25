-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_re_det_gram_le_prod_fin_5585265ad779
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:53:00.613176+00:00
-- url     : https://prove2.me/submissions/bdf56b1c-bdcc-4ee1-91fc-c505a91923a0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHadamardMean
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_norm_sub_starProjection_le_3aef9f9941fc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_det_gram_comp_equiv_8c428ade5abb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_det_gram_sumElim_eq_dfad27be450d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_det_gram_unique_1911557ddd21


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField Matrix GroundTheory.Heights₂.Heights
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
theorem _root_.solution : ∀ (n : ℕ) (c : Fin n → V),
    (det (gram ℂ c)).re ≤ ∏ i, ‖c i‖ ^ 2 := by
  intro n
  induction n with
  | zero => intro c; simp
  | succ n ih =>
    intro c
    let e : Fin n ⊕ Unit ≃ Fin (n + 1) :=
      (Equiv.sumCongr (Equiv.refl _) finOneEquiv.symm).trans finSumFinEquiv
    have he : c ∘ e = Sum.elim (fun i ↦ c i.castSucc) (fun _ : Unit ↦ c (Fin.last n)) := by
      funext b
      rcases b with i | u
      · rfl
      · simp only [Function.comp_apply, Sum.elim_inr]
        congr 1
    have key : det (gram ℂ c) = det (gram ℂ fun i : Fin n ↦ c i.castSucc) *
        ((‖c (Fin.last n) - (Submodule.span ℂ (Set.range fun i : Fin n ↦ c i.castSucc)).starProjection
          (c (Fin.last n))‖ ^ 2 : ℝ) : ℂ) := by
      rw [← det_gram_comp_equiv e c, he, det_gram_sumElim_eq, det_gram_unique]
    rw [key, Complex.re_mul_ofReal, Fin.prod_univ_castSucc]
    exact mul_le_mul (ih _)
      (pow_le_pow_left₀ (norm_nonneg _) (norm_sub_starProjection_le _ _) 2) (sq_nonneg _)
      (Finset.prod_nonneg fun i _ ↦ sq_nonneg _)
end GroundTheory.Heights₂.Heights.LatticeLemmas
