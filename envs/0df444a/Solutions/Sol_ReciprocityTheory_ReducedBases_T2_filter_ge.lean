-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.filter_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:03:47.703332+00:00
-- url     : https://prove2.me/submissions/47fcd1e8-1c47-4ba1-8a15-b8ab3ee055f8

import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt
import Definitions.Def_ReciprocityTheory_ReducedBases_ExistsBoundedBasis
import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
namespace ReciprocityTheory.ReducedBases.T2
theorem _root_.solution (n : ℕ) (h : n < d) :
    univ.filter (fun j : Fin d => n ≤ j.val) =
      insert ⟨n, h⟩ (univ.filter (fun j : Fin d => n + 1 ≤ j.val)) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, Fin.val_mk]
  omega
end ReciprocityTheory.ReducedBases.T2
