-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.filter_le_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:03:51.452799+00:00
-- url     : https://prove2.me/submissions/c7f484ed-4e35-4b02-8602-a0413c80ff62

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
theorem _root_.solution (n : ℕ) (h : n + 1 < d) :
    univ.filter (fun j : Fin d => j.val ≤ n + 1) =
      insert ⟨n + 1, h⟩ (univ.filter (fun j : Fin d => j.val ≤ n)) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, Fin.val_mk]
  omega
end ReciprocityTheory.ReducedBases.T2
