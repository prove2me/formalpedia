-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.dp_card_blkA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:49:53.734583+00:00
-- url     : https://prove2.me/submissions/54a3bf31-93e5-44c4-9457-0167573fd1d8

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DpDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ContDiff ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {j : ℕ} (hj : j ≤ n) : Fintype.card (blkA (n := n) j) = j := by
  rw [Fintype.card_coe]
  have : blkA (n := n) j = Finset.image (Fin.castLE hj) Finset.univ := by
    ext i
    simp only [blkA, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h; exact ⟨⟨i, h⟩, Fin.ext rfl⟩
    · rintro ⟨a, -, rfl⟩; exact a.isLt
  rw [this, Finset.card_image_of_injective _ (Fin.castLE_injective hj), Finset.card_univ, Fintype.card_fin]
end PositivityTheory.Rg.Sw.LVs
