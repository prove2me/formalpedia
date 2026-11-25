-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.RankA.col_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:34:26.519034+00:00
-- url     : https://prove2.me/submissions/d1110129-1ed2-4c79-81ce-dbdbffb3e74e

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_RankMapLeRank

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
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.RankA
variable {S : Type} [CommRing S]
namespace ReciprocityTheory.PGsh.Up.RankA
theorem _root_.solution {m n : Type} [Fintype n] [DecidableEq n] (A : Matrix m n S) (y : n) :
    (fun x => A x y) ∈ LinearMap.range A.mulVecLin :=
  ⟨Pi.single y 1, by ext x; simp⟩
end ReciprocityTheory.PGsh.Up.RankA
