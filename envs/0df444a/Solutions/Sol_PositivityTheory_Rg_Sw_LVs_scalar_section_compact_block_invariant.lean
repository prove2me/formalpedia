-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.scalar_section_compact_block_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:47:28.433194+00:00
-- url     : https://prove2.me/submissions/164a6e74-e327-4ef6-844e-19fd2e72f850

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulConjTransposeEq
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution (hU : UAct) (j : ℕ) (p q : ℤ) (x : M2 n)
    (P' S' : Matrix (Fin n) (Fin n) ℂ) (hP : ∀ a b, P' a b ≠ 0 → a ∈ blkA j ∧ b ∈ blkB j)
    (hS : ∀ a b, S' a b ≠ 0 → a ∈ blkB j ∧ b ∈ blkA j) : f0 p q (x * mX (1 + P') 0 0 (1 + S')) = f0 p q x := by
  have hmA : ∀ a : Fin n, a ∈ blkA j ↔ (a : ℕ) < j := fun a => by simp [blkA]
  have hmB : ∀ a : Fin n, a ∈ blkB j ↔ ¬ (a : ℕ) < j := fun a => by simp [blkB, blkA]
  have dP : (1 + P').det = 1 := by
    rw [Matrix.det_of_upperTriangular]
    · refine Finset.prod_eq_one fun i _ => ?_
      have : P' i i = 0 := by
        by_contra h0
        have := hP i i h0
        exact ((hmB i).1 this.2) ((hmA i).1 this.1)
      simp [this]
    · intro a b hba
      have hab : a ≠ b := fun h => (lt_irrefl _ (h ▸ hba))
      simp only [Matrix.add_apply, Matrix.one_apply_ne hab, zero_add]
      by_contra h0
      have := hP a b h0
      exact ((hmB b).1 this.2) (lt_trans (Fin.lt_def.1 hba) ((hmA a).1 this.1))
  have dS : (1 + S').det = 1 := by
    rw [← det_transpose, Matrix.transpose_add, Matrix.transpose_one, Matrix.det_of_upperTriangular]
    · refine Finset.prod_eq_one fun i _ => ?_
      have : S' i i = 0 := by
        by_contra h0
        have := hS i i h0
        exact ((hmB i).1 this.1) ((hmA i).1 this.2)
      simp [this]
    · intro a b hba
      have hab : a ≠ b := fun h => (lt_irrefl _ (h ▸ hba))
      simp only [Matrix.add_apply, Matrix.one_apply_ne hab, zero_add, Matrix.transpose_apply]
      by_contra h0
      have := hS b a h0
      exact ((hmB b).1 this.1) (lt_trans (Fin.lt_def.1 hba) ((hmA a).1 this.2))
  obtain ⟨e1, e2⟩ := hU n x (1 + P') 0 0 (1 + S')
  rw [f0, f0, e1, e2]
  simp only [Matrix.mul_zero, add_zero, zero_add, det_mul, dP, dS, mul_one]
end PositivityTheory.Rg.Sw.LVs
