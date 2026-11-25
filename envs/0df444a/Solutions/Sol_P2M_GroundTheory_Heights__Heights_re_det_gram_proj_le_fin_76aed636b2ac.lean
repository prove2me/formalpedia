-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_re_det_gram_proj_le_fin_76aed636b2ac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:01:21.145914+00:00
-- url     : https://prove2.me/submissions/287dd6dd-87f6-42ab-98e6-bcfe64998800

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_det_gram_sumElim_eq_dfad27be450d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_det_gram_unique_1911557ddd21
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_det_gram_re_nonneg_5b1b926b272e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_det_gram_comp_equiv_8c428ade5abb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_norm_sub_proj_map_le_249919fb2b52

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
open scoped ComplexOrder
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (Y : Submodule ℂ V) [Y.HasOrthogonalProjection] :
    ∀ (n : ℕ) (c : Fin n → V),
      (det (gram ℂ fun i ↦ Y.starProjection (c i))).re ≤ (det (gram ℂ c)).re := by
  intro n
  induction n with
  | zero => intro c; simp
  | succ n ih =>
    intro c
    let e : Fin n ⊕ Unit ≃ Fin (n + 1) :=
      (Equiv.sumCongr (Equiv.refl _) finOneEquiv.symm).trans finSumFinEquiv
    have he : ∀ (w : Fin (n + 1) → V), w ∘ e =
        Sum.elim (fun i ↦ w i.castSucc) (fun _ : Unit ↦ w (Fin.last n)) := by
      intro w
      funext b
      rcases b with i | u
      · rfl
      · simp only [Function.comp_apply, Sum.elim_inr]
        congr 1
    have key : ∀ (w : Fin (n + 1) → V), det (gram ℂ w) = det (gram ℂ fun i : Fin n ↦ w i.castSucc) *
        ((‖w (Fin.last n) - (Submodule.span ℂ (Set.range fun i : Fin n ↦ w i.castSucc)).starProjection
          (w (Fin.last n))‖ ^ 2 : ℝ) : ℂ) := by
      intro w
      rw [← det_gram_comp_equiv e w, he, det_gram_sumElim_eq, det_gram_unique]
    rw [key c, key (fun i ↦ Y.starProjection (c i))]
    have hc' := ih (fun i : Fin n ↦ c i.castSucc)
    simp only [Complex.re_mul_ofReal]
    have hn := norm_sub_proj_map_le Y (fun i : Fin n ↦ c i.castSucc) (c (Fin.last n))
    exact mul_le_mul hc' (pow_le_pow_left₀ (norm_nonneg _) hn 2) (sq_nonneg _)
      (det_gram_re_nonneg _)
end GroundTheory.Heights₂.Heights
