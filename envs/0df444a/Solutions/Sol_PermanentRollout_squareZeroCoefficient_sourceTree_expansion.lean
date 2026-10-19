-- Prove2me | solution 1 for PermanentRollout.squareZeroCoefficient_sourceTree_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/72ac20c5-409f-433e-a494-5fe2ecf74c8d

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_squareZero_subtreeLinearFormProduct_eq_expansion
import Theorems.Thm_PermanentRollout_sourceRowBlock_card
import Theorems.Thm_PermanentRollout_squareZeroCoefficient_sourceExceptionalBlock

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
    squareZeroCoefficient (b * t)
        ((Finset.univ : Finset (Fin (b * t))) \ omitted)
        (subtreeLinearFormProduct
          (fun h => squareZeroBlockSum (b * t) (sourceRowBlock b t h))
          t d ζ tree) =
      ∑ h : Fin b,
        subtreeCoefficient
            (((-1 : ℂ) ^ (d + 1)) * (2 : ℂ) ^ d) tree h *
          if omitted ⊆ sourceRowBlock b t h then
            ((t.factorial ^ (b - 1) : ℕ) : ℂ) *
              (((t - d).factorial : ℕ) : ℂ)
          else 0 := by
  classical
  rw [squareZero_subtreeLinearFormProduct_eq_expansion
    (b * t) (sourceRowBlock b t) tree t d hdpos hd hζ hnodup
    (fun h _ => sourceRowBlock_card b t h), hleaves, map_sum]
  apply Finset.sum_congr rfl
  intro h _
  rw [← Algebra.smul_def, map_smul,
    squareZeroCoefficient_sourceExceptionalBlock
    b t d omitted homitted h]
  rfl
end PermanentRollout
