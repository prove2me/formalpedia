-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_conj_harm_of_span__62df867434b0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:14:07.251583+00:00
-- url     : https://prove2.me/submissions/cd66477c-3756-48ff-9228-a82977ce51f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsConjHarmOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsConjHarmOfSpanStatement
import Theorems.Thm_GlobalTheory_ClassFin_exists_conj_harm_of_span


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type) [Fintype σ] (τ : σ ≃ σ) (g : σ → Matrix ι ι ℂ), (∀ s, g (τ s) * g s = 1) → Submodule.span ℂ (Set.range g) = ⊤ → ∃ P : Matrix ι ι ℂ, IsUnit P.det ∧ Harm (fun s => P * g s * P⁻¹) := by
  first | exact @GlobalTheory.ClassFin.exists_conj_harm_of_span | exact GlobalTheory.ClassFin.exists_conj_harm_of_span | (intros; apply GlobalTheory.ClassFin.exists_conj_harm_of_span <;> assumption)
end _root_.GlobalTheory.T
