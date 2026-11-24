-- Prove2me | solution 1 for ULHC.theoremA2_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:23:38.746544+00:00
-- url     : https://prove2.me/submissions/3261f131-5b3e-40e2-bd79-678d56cd7ca0

import Definitions.Def_ULHC_Dual
import Definitions.Def_ULHC_V2Seq
import Theorems.Thm_ULHC_typeIII_strip_at
import Theorems.Thm_ULHC_one_strip_P
import Theorems.Thm_ULHC_notTypeIII_of_no
import Theorems.Thm_ULHC_Adj_mono
import Theorems.Thm_ULHC_Conn_mono
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Inside_mono
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_chain_border
import Theorems.Thm_ULHC_closed_cls
import Theorems.Thm_ULHC_conn_of_ncomp_one
import Theorems.Thm_ULHC_deg2_flipCol
import Theorems.Thm_ULHC_end_inter
import Theorems.Thm_ULHC_even_strip_count
import Theorems.Thm_ULHC_exists_not_conn
import Theorems.Thm_ULHC_isEdge_side
import Theorems.Thm_ULHC_lemma57
import Theorems.Thm_ULHC_mem_GE
import Theorems.Thm_ULHC_mem_cells
import Theorems.Thm_ULHC_mem_cls_self
import Theorems.Thm_ULHC_on_chain_of_side
import Theorems.Thm_ULHC_side_mem_cellE
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {H : Finset Edge}
  (hs : Solid V) (hH : Deg2 V H) (hHam : ncomp V H = 1)
include hs hH hHam
namespace ULHC
theorem _root_.solution : ∀ m (F : Finset Edge) (a : Option Pt), mu V F H = m → Deg2 V F →
    2 ≤ ncomp V F → AnchorOK V F a → ∃ L : List StripSpec, ValidSeqA V a F L := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro F a hm hF h2 ha
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_not_conn h2
  have hconn : ∀ z ∈ V, Conn (GE V) x z := fun z hz =>
    (conn_of_ncomp_one hHam hx hz).mono (fun e he => mem_GE.2 (hH.1 e he))
  by_cases hT : NoTypeIII V F
  · -- The border to walk on: a class, or the anchor's chain.
    obtain ⟨P, hB, x', hx', y', hy', hxP, hyP, hon⟩ : ∃ P, Border V F P ∧ ∃ x' ∈ V, ∃ y' ∈ V,
        x' ∈ P ∧ y' ∉ P ∧ ∀ c si, IsCell V c → Cut P (sideEdge c si) → OnChain V F a c := by
      cases a with
      | none =>
        refine ⟨cls V F x, ⟨Finset.filter_subset _ _, fun u hu w hw => closed_cls hF.1 x u hu w hw⟩,
          x, hx, y, hy, mem_cls_self hx, ?_, fun _ _ _ _ => trivial⟩
        simp only [cls, Finset.mem_filter, not_and]; exact fun _ => hxy
      | some u =>
        obtain ⟨⟨e, he⟩, _⟩ := ha
        obtain ⟨P, hB, hcut⟩ := chain_border hs hF hT x hconn u
        have heE : IsEdge V e := by
          simp only [EB, Finset.mem_filter] at he; exact mem_GE.1 he.1
        have hc := (hcut e heE).2 he
        unfold Cut at hc
        refine ⟨P, hB, ?_⟩
        by_cases hp : e.p ∈ P
        · exact ⟨e.p, heE.1, e.q, heE.2, hp, hc.1 hp, fun c si hcell hct =>
            on_chain_of_side hcell (side_mem_cellE c si) ((hcut _ (isEdge_side hcell si)).1 hct)⟩
        · exact ⟨e.q, heE.2, e.p, heE.1, by tauto, hp, fun c si hcell hct =>
            on_chain_of_side hcell (side_mem_cellE c si) ((hcut _ (isEdge_side hcell si)).1 hct)⟩
    obtain ⟨σ, hv, hn2, hmu, si, hcut⟩ := one_strip_P hs hH hHam hF hT hB hx' hy' hxP hyP
    have hc0 : IsCell V σ.c := by
      have := hv.2.2.1 0 (by omega); rwa [cellJ_zero] at this
    have hσon := hon σ.c si hc0 hcut
    rcases Nat.mod_two_eq_zero_or_one σ.n with hev | hodd
    · -- Even: recurse with the end cell as anchor.
      obtain ⟨_, hpat, hcell, hsep⟩ := hv
      obtain ⟨k, hk⟩ : ∃ k, σ.n = k + 2 := ⟨σ.n - 2, by omega⟩
      have hF' : Deg2 V (applyS F σ) := deg2_flipCol _ F hF hpat hcell
      have hcnt := even_strip_count hF hT ⟨by omega, hpat, hcell, hsep⟩ hev
      have hend : endCell σ = cellJ σ.c σ.s (k + 1) := by
        unfold endCell; rw [hk]; rfl
      have hcell' : ∀ j ≤ k + 1, IsCell V (cellJ σ.c σ.s j) := fun j hj => hcell j (by omega)
      rw [hk] at hpat
      have hk2 : k % 2 = 0 := by omega
      have hA : AnchorOK V (applyS F σ) (some (endCell σ)) := by
        unfold applyS
        rw [hk, hend]
        refine ⟨⟨_, (end_inter hF hT hk2 hcell' hpat hsep).2⟩, fun hT' => ?_⟩
        obtain ⟨d, hd, hd3⟩ := notTypeIII_of_no hT'
        exact lemma57 hF hT hk2 hcell' hpat hsep hs x hconn hd hd3
      obtain ⟨L', hL'⟩ := ih (mu V (applyS F σ) H) (by omega) (applyS F σ) _ rfl hF'
        (by omega) hA
      rcases L' with _ | ⟨τ, L'⟩
      · exact hL'.elim
      · exact ⟨σ :: τ :: L', ⟨by omega, by rw [hk]; exact hpat, hcell, hsep⟩, hev, hT, hσon, hL'⟩
    · exact ⟨[σ], hv, hodd, hσon⟩
  · -- A Type III cell, on the anchor's chain if there is an anchor.
    cases a with
    | none =>
      obtain ⟨d, hd, hd3⟩ := notTypeIII_of_no hT
      obtain ⟨σ, _, hv, hodd⟩ := typeIII_strip_at hd hd3
      exact ⟨[σ], hv, hodd, trivial⟩
    | some u =>
      obtain ⟨d, hdc, hd3⟩ := ha.2 hT
      have hd : IsCell V d := by
        simp only [chainCells, Finset.mem_filter] at hdc; exact mem_cells.1 hdc.1
      obtain ⟨σ, hσc, hv, hodd⟩ := typeIII_strip_at hd hd3
      exact ⟨[σ], hv, hodd, by show σ.c ∈ chainCells V F u; rw [hσc]; exact hdc⟩
end ULHC
