-- Prove2me | solution 1 for TDLC.Path.parity_lEmbed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:24:33.391869+00:00
-- url     : https://prove2.me/submissions/07601219-a306-4ed3-ae73-15c9b51384d8


import Definitions.Def_TDLC_Solution
import Theorems.Thm_TDLC_bxor_false_right
attribute [local simp] TDLC.bxor_false_right

set_option autoImplicit true
open TDLC
universe u
namespace TDLC
namespace Path
theorem _root_.solution {A : Type u} {x y : A} (s : Step x y) :
    Path.parity (Path.lEmbed s) = Step.parity s := by
  change bxor (Step.parity s) false = Step.parity s
  exact bxor_false_right _
end Path
end TDLC
