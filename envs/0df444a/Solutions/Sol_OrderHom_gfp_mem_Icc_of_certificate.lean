-- Prove2me | solution 1 for OrderHom.gfp_mem_Icc_of_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:25:48.731837+00:00
-- url     : https://prove2.me/submissions/900b8078-f772-4e16-a6a2-8e50062f0be8

import Definitions.Def_Csg_ReachOp
import Definitions.Def_Csg_SafetyOp
import Definitions.Def_Csg_IntervalCertificate

set_option autoImplicit true

namespace OrderHom
theorem _root_.solution {α : Type*} [CompleteLattice α] (f : α →o α)
    (lo hi : α) (hpost : lo ≤ f lo) (hub : ∀ b, b ≤ f b → b ≤ hi) :
    lo ≤ f.gfp ∧ f.gfp ≤ hi :=
  ⟨f.le_gfp hpost, f.gfp_le hub⟩
end OrderHom
