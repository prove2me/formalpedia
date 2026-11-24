-- Prove2me | solution 1 for ULHC.path_to_crpath
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:13:43.418658+00:00
-- url     : https://prove2.me/submissions/636bfad8-92bc-41aa-9861-3fceea0eec24

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_LinkGraph
import Theorems.Thm_ULHC_pw_posList
import Theorems.Thm_ULHC_chain_of_tail
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_MP_isPath_cons
import Theorems.Thm_ULHC_NoTypeIII_at
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
theorem _root_.solution (hGV : Inside V G) {p : List Node}
    (hp : MP.IsPath (gsrc V G) gmid gtgt (gedge V G) p) (hN : ∀ x ∈ p, x ∈ candN V G) :
    ∃ σ L, p = posList 1 (σ :: L) ∧ CRPathCA V G σ L ∧ MP.pw gw p = wt σ L := by
  cases p with
  | nil => exact absurd hp id
  | cons x rest =>
    obtain ⟨σ, k⟩ := x
    rw [MP.isPath_cons] at hp
    obtain ⟨hs, ht⟩ := hp
    simp only [gsrc, Bool.and_eq_true, beq_iff_eq] at hs
    obtain ⟨rfl, hv⟩ := hs
    rw [validB_iff hGV] at hv
    obtain ⟨L, hL, hch, hnc⟩ := chain_of_tail hGV rest ⟨σ, 1⟩ ht hN
    subst hL
    refine ⟨σ, L, rfl, ⟨⟨hv, hch⟩, hnc⟩, ?_⟩
    rw [show (⟨σ, 1⟩ :: posList (min (1 + 1) 3) L : List Node) = posList 1 (σ :: L) from rfl,
      pw_posList]
    rfl
end ULHC
