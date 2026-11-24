-- Prove2me | solution 1 for ULHC.Conn.trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:39:43.328315+00:00
-- url     : https://prove2.me/submissions/6ecba9ae-6819-46d4-8ba9-64918841826f

import Definitions.Def_ULHC_D
import Definitions.Def_ULHC_Conn

set_option autoImplicit true
open ULHC
namespace ULHC
namespace Conn
theorem _root_.solution {F : Finset Edge} {a b c : Pt} (h1 : Conn F a b) (h2 : Conn F b c) :
    Conn F a c := Relation.ReflTransGen.trans h1 h2
end Conn
end ULHC
