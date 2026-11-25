-- Prove2me | solution 1 for P2M_GlobalTheory_T_entries_bounded_of_conj_spanning_bounded__a0549da12fe9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:33:59.493546+00:00
-- url     : https://prove2.me/submissions/250eef9a-9bf8-4781-b128-e842c9da0a4d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EntriesBoundedOfConjSpanningBounded
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EntriesBoundedOfConjSpanningBoundedStatement
import Theorems.Thm_GlobalTheory_ClassFin_entries_bounded_of_conj_spanning_bounded


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
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type) [Fintype σ] (g : σ → Matrix ι ι ℂ), Submodule.span ℂ (Set.range g) = ⊤ → ∀ C : ℝ, ∃ C' : ℝ, ∀ P : Matrix ι ι ℂ, P.det = 1 → (∀ s i j, ‖(P * g s * P⁻¹) i j‖ ≤ C) → ∀ i j, ‖P i j‖ ≤ C' := by
  first | exact @GlobalTheory.ClassFin.entries_bounded_of_conj_spanning_bounded | exact GlobalTheory.ClassFin.entries_bounded_of_conj_spanning_bounded | (intros; apply GlobalTheory.ClassFin.entries_bounded_of_conj_spanning_bounded <;> assumption)
end _root_.GlobalTheory.T
