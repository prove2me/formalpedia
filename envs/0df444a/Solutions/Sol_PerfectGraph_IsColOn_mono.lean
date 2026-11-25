-- Prove2me | solution 1 for PerfectGraph.IsColOn.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:34:01.182816+00:00
-- url     : https://prove2.me/submissions/d7112d4f-0e02-4a31-ba5e-4b415cc22339

module
public import Mathlib
public import Definitions.Def_PerfectLib_Gasparian

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open PerfectGraph
variable {V : Type*} (G : SimpleGraph V)
namespace PerfectGraph
namespace IsColOn
theorem _root_.solution {S : Finset V} {k l : ℕ} (h : IsColOn G S k) (hkl : k ≤ l) :
    IsColOn G S l := by
  obtain ⟨c, hc, hv⟩ := h
  exact ⟨c, fun v hv => (hc v hv).trans_le hkl, hv⟩
end IsColOn
end PerfectGraph
