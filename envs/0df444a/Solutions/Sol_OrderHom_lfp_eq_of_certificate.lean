-- Prove2me | solution 1 for OrderHom.lfp_eq_of_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:52:58.488496+00:00
-- url     : https://prove2.me/submissions/8da48b1d-c0b6-4be6-a5fd-2cec79a95924

import Definitions.Def_Csg_ReachOp
import Definitions.Def_Csg_ReachCertificate

set_option autoImplicit true

namespace OrderHom
theorem _root_.solution {α : Type*} [CompleteLattice α] (f : α →o α) (v : α)
    (hfixed : f v = v) (hlb : ∀ b, f b ≤ b → v ≤ b) : f.lfp = v :=
  le_antisymm (f.lfp_le_fixed hfixed) (f.le_lfp hlb)
end OrderHom
