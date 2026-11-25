-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.Act.C4.Bq.NQ.upper_block_rank_one_update
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:55:21.539631+00:00
-- url     : https://prove2.me/submissions/d5d193f7-5b02-4b4d-8fd4-e0ee82ca7d01

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ParabolicBlockForms_UpperBlockRankOneUpdate
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_Act_C4_Bq_NQ_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.Act PositivityTheory.SiegelWeilFormula.Act.C4 PositivityTheory.SiegelWeilFormula.Act.C4.Bq
open Matrix
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
variable {n : ℕ}
namespace PositivityTheory.SiegelWeilFormula.Act.C4.Bq
namespace NQ
theorem _root_.solution {i₀ : Fin n} {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R} (hM : NQ (Sum.inl i₀) (Sum.inr i₀) M) :
    M.toBlocks₁₁ = 1 + replicateCol Unit (Pi.single i₀ (1 : R)) * replicateRow Unit (fun k => (M - 1) (Sum.inl i₀) (Sum.inl k)) := by
  refine Matrix.ext fun a k => ?_
  simp only [Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply, replicateCol_apply,
    replicateRow_apply, Finset.univ_unique, Finset.sum_singleton]
  by_cases ha : a = i₀
  · subst ha
    simp only [Pi.single_eq_same, one_mul, Matrix.sub_apply]
    rw [Matrix.one_apply, Matrix.one_apply]
    by_cases hk : a = k
    · subst hk; simp
    · simp [hk]
  · rw [Pi.single_eq_of_ne ha, zero_mul, add_zero]
    by_cases hk : k = i₀
    · subst hk; rw [hM.apply (Or.inl rfl)]; simp [Matrix.one_apply]
    · rw [hM.apply (Or.inr ⟨by simp, by simpa using ha⟩)]; simp [Matrix.one_apply]
end NQ
end PositivityTheory.SiegelWeilFormula.Act.C4.Bq
