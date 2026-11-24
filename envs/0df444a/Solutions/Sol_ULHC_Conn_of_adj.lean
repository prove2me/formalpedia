-- Prove2me | solution 1 for ULHC.Conn.of_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:40:50.535936+00:00
-- url     : https://prove2.me/submissions/414ec89a-4fcc-4bb3-aa84-9a3f9c0f5aaf

import Definitions.Def_ULHC_D
import Definitions.Def_ULHC_Conn

set_option autoImplicit true
open ULHC
namespace ULHC
namespace Conn
theorem _root_.solution {F : Finset Edge} {a b : Pt} (h : Adj F a b) : Conn F a b :=
  Relation.ReflTransGen.single h
end Conn
end ULHC
