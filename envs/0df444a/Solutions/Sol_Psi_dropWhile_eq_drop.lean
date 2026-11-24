-- Prove2me | solution 1 for Psi.dropWhile_eq_drop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:42:44.844419+00:00
-- url     : https://prove2.me/submissions/3e18cd18-c7b4-445b-85b1-eff22eb10ff6

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution {α} (p : α → Bool) (l : List α) :
    l.dropWhile p = l.drop (l.takeWhile p).length := by
  have h := List.takeWhile_append_dropWhile (p := p) (l := l)
  calc l.dropWhile p = (l.takeWhile p ++ l.dropWhile p).drop (l.takeWhile p).length := by
          rw [List.drop_left]
    _ = l.drop (l.takeWhile p).length := by rw [h]
end Psi
