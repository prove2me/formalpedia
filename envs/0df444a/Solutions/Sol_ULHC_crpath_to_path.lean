-- Prove2me | solution 1 for ULHC.crpath_to_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:15:12.13035+00:00
-- url     : https://prove2.me/submissions/a12657a9-4978-4e92-ae69-9d21f285197f

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_LinkGraph
import Theorems.Thm_ULHC_pw_posList
import Theorems.Thm_ULHC_posList_mem
import Theorems.Thm_ULHC_mem_candN
import Theorems.Thm_ULHC_valid_cells
import Theorems.Thm_ULHC_cand_of_valid
import Theorems.Thm_ULHC_chain_cand
import Theorems.Thm_ULHC_tail_of_chain
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_MP_isPath_cons
import Theorems.Thm_ULHC_validB_iff
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
theorem _root_.solution (hGV : Inside V G) {σ : StripSpec} {L : List StripSpec}
    (h : CRPathCA V G σ L) :
    MP.IsPath (gsrc V G) gmid gtgt (gedge V G) (posList 1 (σ :: L)) ∧
      (∀ x ∈ posList 1 (σ :: L), x ∈ candN V G) ∧ MP.pw gw (posList 1 (σ :: L)) = wt σ L := by
  obtain ⟨⟨hv, hch⟩, hnc⟩ := h
  obtain ⟨h1, hc⟩ := valid_cells hv
  refine ⟨?_, ?_, ?_⟩
  · rw [posList, MP.isPath_cons]
    refine ⟨?_, tail_of_chain hGV L σ 1 h1 hc hch hnc⟩
    show ((1 == 1) && validB V G σ) = true
    rw [(validB_iff hGV).2 hv]
    rfl
  · intro x hx
    obtain ⟨hxL, hk1, hk3⟩ := posList_mem (σ :: L) 1 (by omega) x hx
    refine mem_candN.2 ⟨?_, ?_⟩
    · rcases List.mem_cons.1 hxL with he | he
      · rw [he]
        exact cand_of_valid hv
      · exact chain_cand L σ h1 hc hch _ he
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
  · rw [pw_posList]
    rfl
end ULHC
