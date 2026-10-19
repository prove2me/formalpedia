-- Prove2me | solution 1 for PermanentRollout.sourceTreeMatrix_alpha_eq_block_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/eedc2d82-8192-4e05-8ebe-f42211747da8

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_sourceRowBlock_exceptional_unique
import Theorems.Thm_PermanentRollout_sourceTreeMatrix_alpha_eq_zero
import Theorems.Thm_PermanentRollout_sourceTreeMatrix_alpha_eq_factorial

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    (b t d : ℕ) (hdpos : 0 < d) (hd : d ≤ t)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ d)
    (tree : BlockTree (Fin b))
    (hnodup : tree.leafList.Nodup)
    (hleaves : tree.leaves = Finset.univ)
    (omitted : Finset (Fin (b * t)))
    (homitted : omitted.card = d) :
    sourceBlockAlpha (b * t) d
        (sourceTreeMatrix b t d hd ζ tree hnodup hleaves) omitted =
      (((t - d).factorial : ℕ) : ℂ) *
        (((t.factorial : ℕ) : ℂ) ^ (b - 1)) *
        ∑ h : Fin b,
          if omitted ⊆ sourceRowBlock b t h then
            subtreeCoefficient
              (((-1 : ℂ) ^ (d + 1)) * (2 : ℂ) ^ d) tree h
          else 0 := by
  classical
  by_cases hblock : ∃ h : Fin b, omitted ⊆ sourceRowBlock b t h
  · obtain ⟨h, hh⟩ := hblock
    have hnonempty : omitted.Nonempty :=
      Finset.card_pos.mp (homitted.symm ▸ hdpos)
    have hunique : ∀ h' : Fin b,
        (omitted ⊆ sourceRowBlock b t h') ↔ h' = h := by
      intro h'
      constructor
      · intro hh'
        exact sourceRowBlock_exceptional_unique omitted hnonempty hh' hh
      · rintro rfl
        exact hh
    rw [sourceTreeMatrix_alpha_eq_factorial
      b t d hdpos hd hζ tree hnodup hleaves omitted homitted h hh]
    simp_rw [hunique]
    simp [mul_assoc, mul_left_comm, mul_comm]
  · have hnone : ∀ h : Fin b, ¬ omitted ⊆ sourceRowBlock b t h := by
      simpa only [not_exists] using hblock
    rw [sourceTreeMatrix_alpha_eq_zero
      b t d hdpos hd hζ tree hnodup hleaves omitted homitted hnone]
    simp [hnone]
end PermanentRollout
