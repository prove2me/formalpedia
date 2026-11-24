-- Prove2me | solution 1 for ULHC.chain_of_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:11:21.127638+00:00
-- url     : https://prove2.me/submissions/552573ca-945b-416b-9b18-3020d068f94c

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_LinkGraph
import Theorems.Thm_ULHC_chainOKB_iff
import Theorems.Thm_ULHC_mem_candN
import Theorems.Thm_ULHC_cells_of_cand
import Theorems.Thm_ULHC_endCell_isCell
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_MP_isTail_cons
import Theorems.Thm_ULHC_NoTypeIII_at
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
theorem _root_.solution (hGV : Inside V G) : ∀ (rest : List Node) (x : Node),
    MP.IsTail gmid gtgt (gedge V G) x rest → (∀ y ∈ x :: rest, y ∈ candN V G) →
    ∃ L, rest = posList (min (x.pos + 1) 3) L ∧ CRChain V G x.σ L ∧ CATail (x.σ :: L) := by
  intro rest
  induction rest with
  | nil =>
    intro x ht _
    refine ⟨[], rfl, ?_, trivial⟩
    have h : gtgt x = true := ht
    simp only [gtgt, beq_iff_eq] at h
    exact h
  | cons y rest ih =>
    intro x ht hN
    rw [MP.isTail_cons] at ht
    obtain ⟨hm, he, ht'⟩ := ht
    obtain ⟨L, hL, hch, hcat⟩ :=
      ih y ht' (fun z hz => hN z (List.mem_cons_of_mem _ hz))
    obtain ⟨hxc, _⟩ := mem_candN.1 (hN x (by simp))
    obtain ⟨hx1, hxcells⟩ := cells_of_cand hxc
    simp only [gedge, Bool.and_eq_true, beq_iff_eq, chainOKB_iff] at he
    obtain ⟨⟨hpos, hcr⟩, hok⟩ := he
    rw [cr2B_iff hGV (endCell_isCell hx1 hxcells)] at hcr
    have hev : x.σ.n % 2 = 0 := by
      simp only [gmid, beq_iff_eq] at hm
      exact hm
    refine ⟨y.σ :: L, ?_, ?_, hok, hcat⟩
    · rw [posList, ← hpos, ← hL]
    · show x.σ.n % 2 = 0 ∧ CR2 V G x.σ y.σ ∧ CRChain V G y.σ L
      exact ⟨hev, hcr, hch⟩
end ULHC
