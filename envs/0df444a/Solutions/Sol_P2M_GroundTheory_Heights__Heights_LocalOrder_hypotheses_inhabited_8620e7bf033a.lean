-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LocalOrder_hypotheses_inhabited_8620e7bf033a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:58:51.578222+00:00
-- url     : https://prove2.me/submissions/89d94915-154d-4739-bcd1-918dc86b0ff0

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_space_dim_45905c840704
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linForm_one_not_mem_point_805b757dbb4c


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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights
namespace LocalOrder
theorem _root_.solution :
    (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)).IsPrime ∧
      ringKrullDim (MvPolynomial (Fin 1) ℂ ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) ℂ))) = (0 + 1 : ℕ) ∧
      linForm (fun _ : Fin 1 => (1 : ℂ)) ∉ (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) ∧
      (Ideal.span {X 0} : Ideal (MvPolynomial (Fin 1) ℂ)) ∈
        ((⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) ⊔ Ideal.span {linForm fun _ : Fin 1 => (1 : ℂ)}).minimalPrimes ∧
      (0 : Fin 1 → ℂ) ∈ zeroSet (Ideal.span {X 0} : Ideal (MvPolynomial (Fin 1) ℂ)) ∧
      (∃ N ∈ 𝓝 (0 : Fin 1 → ℂ), zeroSet (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) ∩ N ⊆
        ⋃ b : Fin 1, ((fun _ => lineBranch) b).image) ∧
      (∃ N ∈ 𝓝 (0 : Fin 1 → ℂ), ∀ b : Fin 1,
        zeroSet (Ideal.span {X 0} : Ideal (MvPolynomial (Fin 1) ℂ)) ∩ N ⊆
          ((fun _ => lineBranch) b).slice) ∧
      (∀ b b' : Fin 1, b ≠ b' → ((fun _ => lineBranch) b).image ∩ ((fun _ => lineBranch) b').image ⊆
        {x | linEval (fun _ => 1) x = 0}) ∧
      (∀ b : Fin 1, VanishesToOrder (fun t => linEval (fun _ => 1) (((fun _ => lineBranch) b).toFun t))
        ((fun _ => lineBranch) b).radius ((fun _ => 1) b)) := by
  have hl : linForm (fun _ : Fin 1 => (1 : ℂ)) = X 0 := by simp [linForm]
  have hW : (Ideal.span {X 0} : Ideal (MvPolynomial (Fin 1) ℂ)).IsPrime :=
    (Ideal.span_singleton_prime (X_ne_zero _)).mpr X_prime
  have hZ : ∀ x : Fin 1 → ℂ, x ∈ zeroSet (Ideal.span {X 0} : Ideal (MvPolynomial (Fin 1) ℂ)) →
      x = 0 := by
    intro x hx
    have h0 := hx (X 0) (Ideal.subset_span rfl)
    simp only [eval_X] at h0
    funext i
    fin_cases i
    exact h0
  refine ⟨Ideal.isPrime_bot, space_dim 1, linForm_one_not_mem_point ℂ, ?_, ?_,
    ⟨Metric.ball 0 1, Metric.ball_mem_nhds 0 one_pos, fun x hx => Set.mem_iUnion.mpr ⟨0, x, hx.2, rfl⟩⟩,
    ⟨Set.univ, Filter.univ_mem, fun _ x hx => ?_⟩, fun b b' h => absurd (Subsingleton.elim b b') h,
    fun _ => ⟨fun _ => 1, differentiableOn_const _, fun _ _ => one_ne_zero, fun t _ => ?_⟩⟩
  · rw [hl, bot_sup_eq, Ideal.minimalPrimes_eq_subsingleton_self]
    rfl
  · intro q hq
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hq
    simp
  · obtain rfl := hZ x hx.1
    exact ⟨0, ⟨Metric.mem_ball_self lineBranch.radius_pos, rfl⟩, rfl⟩
  · simp [linEval, lineBranch]
end LocalOrder
end GroundTheory.Heights₂.Heights
