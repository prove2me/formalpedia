-- Prove2me | solution 1 for OrderHom.lfp_mem_Icc_of_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:25:42.34832+00:00
-- url     : https://prove2.me/submissions/2eb64d56-3f61-4079-afe3-4f9b5f221c4c

import Definitions.Def_Csg_ReachOp
import Definitions.Def_Csg_SafetyOp
import Definitions.Def_Csg_IntervalCertificate

set_option autoImplicit true

namespace OrderHom
theorem _root_.solution {α : Type*} [CompleteLattice α] (f : α →o α)
    (lo hi : α) (hlb : ∀ b, f b ≤ b → lo ≤ b) (hpre : f hi ≤ hi) :
    lo ≤ f.lfp ∧ f.lfp ≤ hi :=
  ⟨f.le_lfp hlb, f.lfp_le hpre⟩
end OrderHom
