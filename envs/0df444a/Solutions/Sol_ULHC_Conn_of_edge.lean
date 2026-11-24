-- Prove2me | solution 1 for ULHC.Conn.of_edge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:45:08.102008+00:00
-- url     : https://prove2.me/submissions/014e8354-87e7-4771-8a20-55e7d9bc4710

import Definitions.Def_ULHC_D
import Definitions.Def_ULHC_Conn
import Theorems.Thm_ULHC_Conn_of_adj

set_option autoImplicit true
open ULHC
namespace ULHC
namespace Conn
theorem _root_.solution {F : Finset Edge} {e : Edge} (he : e ∈ F) : Conn F e.p e.q :=
  Conn.of_adj ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
end Conn
end ULHC
