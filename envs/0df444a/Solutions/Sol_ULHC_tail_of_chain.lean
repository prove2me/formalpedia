-- Prove2me | solution 1 for ULHC.tail_of_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:11:13.075553+00:00
-- url     : https://prove2.me/submissions/424b86db-fd95-4a56-8ce0-53fbf7a74b2c

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_LinkGraph
import Theorems.Thm_ULHC_chainOKB_iff
import Theorems.Thm_ULHC_endCell_isCell
import Theorems.Thm_ULHC_link_cells
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_MP_isTail_cons
import Theorems.Thm_ULHC_cr2B_iff
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}
namespace ULHC
theorem _root_.solution (hGV : Inside V G) : ∀ (L : List StripSpec) (b : StripSpec) (k : ℕ),
    1 ≤ b.n → (∀ j < b.n, IsCell V (cellJ b.c b.s j)) → CRChain V G b L → CATail (b :: L) →
    MP.IsTail gmid gtgt (gedge V G) ⟨b, k⟩ (posList (min (k + 1) 3) L) := by
  intro L
  induction L with
  | nil =>
    intro b k _ _ hch _
    show gtgt ⟨b, k⟩ = true
    simp only [gtgt, beq_iff_eq]
    exact hch
  | cons c L ih =>
    intro b k h1 hb hch hcat
    obtain ⟨hev, hl, hrest⟩ := hch
    obtain ⟨hc1, hcc⟩ := link_cells hl
    rw [posList, MP.isTail_cons]
    refine ⟨?_, ?_, ih c (min (k + 1) 3) hc1 hcc hrest hcat.2⟩
    · show (b.n % 2 == 0) = true
      simp only [beq_iff_eq]
      exact hev
    · show ((min (k + 1) 3 == min (k + 1) 3) && cr2B V G b c && chainOKB b c) = true
      rw [beq_self_eq_true, (cr2B_iff hGV (endCell_isCell h1 hb)).2 hl, chainOKB_iff.2 hcat.1]
      rfl
end ULHC
