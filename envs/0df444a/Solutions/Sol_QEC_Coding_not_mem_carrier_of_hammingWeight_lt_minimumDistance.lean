-- Prove2me | solution 1 for QEC.Coding.not_mem_carrier_of_hammingWeight_lt_minimumDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:29:13.552108+00:00
-- url     : https://prove2.me/submissions/720bdac3-47cb-43c0-90d3-74e066906719

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions

set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x
namespace QEC.Coding
theorem _root_.solution {F : Type u} {ι : Type v}
    [Field F] [Fintype F] [DecidableEq F] [Fintype ι] {C : LinearCode F ι} {d : Nat}
    (hmin : MinimumDistance C d) {x : Word F ι} (hx0 : x ≠ 0) (hlt : HammingWeight x < d) :
    x ∉ C.carrier := by
  intro hxC
  rcases hmin with ⟨_, _, _, _, hleast⟩
  exact (Nat.not_lt_of_ge (hleast x hxC hx0)) hlt
end QEC.Coding
