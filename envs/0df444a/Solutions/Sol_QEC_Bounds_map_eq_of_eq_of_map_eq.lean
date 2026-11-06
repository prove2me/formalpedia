-- Prove2me | solution 1 for QEC.Bounds.map_eq_of_eq_of_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:06:46.216442+00:00
-- url     : https://prove2.me/submissions/0ec6bff9-2758-44f8-867c-1344816c013c

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_BlockData
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_SecondCutEquality

set_option autoImplicit false
open QEC
open QEC.Bounds
namespace QEC.Bounds
theorem _root_.solution {α β : Type*} (f : α → β) {x y : α} {z : β}
    (hxy : x = y) (hyz : f y = z) : f x = z :=
  (congrArg f hxy).trans hyz
end QEC.Bounds
