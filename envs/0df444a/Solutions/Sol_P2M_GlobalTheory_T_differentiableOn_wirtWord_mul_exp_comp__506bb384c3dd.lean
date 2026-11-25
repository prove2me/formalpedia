-- Prove2me | solution 1 for P2M_GlobalTheory_T_differentiableOn_wirtWord_mul_exp_comp__506bb384c3dd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:19:30.456253+00:00
-- url     : https://prove2.me/submissions/c5a7bd33-4d8d-4425-b413-808cfb16c07c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableOnWirtWordMulExpComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableOnWirtWordMulExpCompStatement
import Theorems.Thm_GlobalTheory_WirtChain_differentiableOn_wirtWord_mul_exp_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (Φ I : Type) [Fintype Φ] [Fintype I] (U : Set (I → ℂ)) (V : Set (Φ → ℂ)) (D : Set ℂ) (G : ℂ → (Φ → ℂ) → ℂ) (t : (I → ℂ) → Φ → ℂ) (b l : (I → ℂ) → ℂ), IsOpen U → IsOpen V → Set.MapsTo t U V → ContDiffOn ℝ ∞ t U → ContDiffOn ℝ ∞ b U → ContDiffOn ℝ ∞ l U → (∀ σ ∈ D, ContDiffOn ℝ ∞ (G σ) V) → (∀ w : List (Φ × Bool), ∀ y ∈ V, DifferentiableOn ℂ (fun σ => wirtWord w (G σ) y) D) → ∀ w : List (I × Bool), ∀ z ∈ U, DifferentiableOn ℂ (fun σ => wirtWord w (fun z' => b z' * Complex.exp (-σ * l z') * G σ (t z')) z) D := by
  first | exact @GlobalTheory.WirtChain.differentiableOn_wirtWord_mul_exp_comp | exact GlobalTheory.WirtChain.differentiableOn_wirtWord_mul_exp_comp | (intros; apply GlobalTheory.WirtChain.differentiableOn_wirtWord_mul_exp_comp <;> assumption)
end _root_.GlobalTheory.T
