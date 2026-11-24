-- Prove2me | solution 1 for ULHC.Conn.refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:40:53.43184+00:00
-- url     : https://prove2.me/submissions/24b0a796-7c13-4dd5-977b-0f7be71201c4

import Definitions.Def_ULHC_D
import Definitions.Def_ULHC_Conn

set_option autoImplicit true
open ULHC
namespace ULHC
namespace Conn
theorem _root_.solution (F : Finset Edge) (a : Pt) : Conn F a a := Relation.ReflTransGen.refl
end Conn
end ULHC
