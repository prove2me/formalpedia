-- Prove2me | solution 1 for PermanentRollout.squareZeroCoefficient_sourceTree_eq_factorial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/6e67af52-abf1-424d-a8e6-b1f2ca4d7ff1

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_squareZeroCoefficient_sourceTree_expansion
import Theorems.Thm_PermanentRollout_sourceRowBlock_exceptional_unique

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
    (homitted : omitted.card = d) (h : Fin b)
    (hsubset : omitted ⊆ sourceRowBlock b t h) :
    squareZeroCoefficient (b * t)
        ((Finset.univ : Finset (Fin (b * t))) \ omitted)
        (subtreeLinearFormProduct
          (fun j => squareZeroBlockSum (b * t) (sourceRowBlock b t j))
          t d ζ tree) =
      subtreeCoefficient
          (((-1 : ℂ) ^ (d + 1)) * (2 : ℂ) ^ d) tree h *
        (((t - d).factorial : ℕ) : ℂ) *
        (((t.factorial : ℕ) : ℂ) ^ (b - 1)) := by
  classical
  have hnonempty : omitted.Nonempty := by
    rw [← Finset.card_pos]
    omega
  rw [squareZeroCoefficient_sourceTree_expansion
    b t d hdpos hd hζ tree hnodup hleaves omitted homitted,
    Finset.sum_eq_single h]
  · simp [hsubset, Nat.cast_pow]
    ring
  · intro j _ hj
    have hother : ¬omitted ⊆ sourceRowBlock b t j := by
      intro hother
      exact hj (sourceRowBlock_exceptional_unique omitted
        hnonempty hother hsubset)
    simp [hother]
  · simp
end PermanentRollout
