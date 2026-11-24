-- Prove2me | solution 1 for ULHC.APair.flip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:15:08.107913+00:00
-- url     : https://prove2.me/submissions/c0ca2d6e-62c9-4e24-aaae-3d3e72ed63f6

import Definitions.Def_ULHC_Flip
import Definitions.Def_ULHC_AFlip
import Theorems.Thm_ULHC_Ends_inc_iff
import Theorems.Thm_ULHC_Ends_conn
import Theorems.Thm_ULHC_Ends_ne
import Theorems.Thm_ULHC_Ends_insert_conn
import Theorems.Thm_ULHC_Ends_merge
import Theorems.Thm_ULHC_ACell_merge
import Theorems.Thm_ULHC_Ends_swap
import Theorems.Thm_ULHC_Ends_ne_of
import Theorems.Thm_ULHC_inc_of_deg_two
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_closed_conn
import Theorems.Thm_ULHC_conn_insert
import Theorems.Thm_ULHC_ncomp_congr
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} (P : APair)
  (hV : Inside V F) (hVa : P.a ∈ V) (hVb : P.b ∈ V) (hVm1 : P.m1 ∈ V) (hVm2 : P.m2 ∈ V)
  (hVt1 : P.t1 ∈ V) (hVt2 : P.t2 ∈ V)
  (heam : P.eam ∈ F) (hebm : P.ebm ∈ F) (hem : P.em ∈ F) (het : P.et ∈ F)
  (hd1 : deg F P.m1 = 2) (hd2 : deg F P.m2 = 2)
include hV hVa hVb hVm1 hVm2 hVt1 hVt2 heam hebm hem het hd1 hd2
omit hV hVa hVt2
namespace ULHC
namespace APair
theorem _root_.solution :
    ncomp V (P.res F) = ncomp V F ∧
      ∀ x y, x ≠ P.m1 → x ≠ P.m2 → y ≠ P.m1 → y ≠ P.m2 →
        (Conn (P.res F) x y ↔ Conn F x y) := by
  -- Edges at `m1` and `m2` in `F`.
  have neq1 : P.eam ≠ P.em := P.ham.ne_of P.hm P.m2a (fun h => P.hm.ne h.symm)
  have neq2 : P.ebm ≠ P.em := (P.hm.ne_of P.hbm.swap P.m1b.symm P.m2b.symm).symm
  have at1 : ∀ f ∈ F, (f.p = P.m1 ∨ f.q = P.m1) → f = P.eam ∨ f = P.em := fun f hf hz =>
    inc_of_deg_two hd1 heam ((P.ham.inc_iff _).2 (Or.inr rfl)) hem
      ((P.hm.inc_iff _).2 (Or.inl rfl)) neq1 hf hz
  have at2 : ∀ f ∈ F, (f.p = P.m2 ∨ f.q = P.m2) → f = P.ebm ∨ f = P.em := fun f hf hz =>
    inc_of_deg_two hd2 hebm ((P.hbm.inc_iff _).2 (Or.inr rfl)) hem
      ((P.hm.inc_iff _).2 (Or.inr rfl)) neq2 hf hz
  -- Step 1: insert `a–b` (already joined through `m1`, `m2`).
  have cab : Conn F P.a P.b :=
    ((P.ham.conn heam).trans (P.hm.conn hem)).trans (P.hbm.conn hebm).symm
  set F1 := insert P.eab F with hF1
  have c1 : ∀ x y, Conn F1 x y ↔ Conn F x y := P.hab.insert_conn cab
  -- Step 2: erase `a–m1` (still joined through `b`, `m2`).
  have hamF1 : P.eam ∈ F1 := Finset.mem_insert_of_mem heam
  set F2 := F1.erase P.eam with hF2
  have eab_ne : P.eab ≠ P.eam := (P.hab.ne_of P.ham P.m1a P.m1b)
  have cam2 : Conn F2 P.a P.m1 := by
    have s1 : Conn F2 P.a P.b := P.hab.conn (Finset.mem_erase.2 ⟨eab_ne, Finset.mem_insert_self _ _⟩)
    have s2 : Conn F2 P.b P.m2 := P.hbm.conn (Finset.mem_erase.2
      ⟨(P.ham.ne_of P.hbm P.m2a (fun h => P.hm.ne h.symm)).symm, Finset.mem_insert_of_mem hebm⟩)
    have s3 : Conn F2 P.m2 P.m1 :=
      (P.hm.conn (Finset.mem_erase.2 ⟨neq1.symm, Finset.mem_insert_of_mem hem⟩)).symm
    exact (s1.trans s2).trans s3
  have c2 : ∀ x y, Conn F2 x y ↔ Conn F1 x y := by
    intro x y
    have := P.ham.insert_conn cam2 x y
    rw [Finset.insert_erase hamF1] at this
    exact this.symm
  -- Step 3: erase `b–m2`; now `{m1, m2}` is a class of its own.
  have hebmF2 : P.ebm ∈ F2 := Finset.mem_erase.2
    ⟨(P.ham.ne_of P.hbm P.m2a (fun h => P.hm.ne h.symm)).symm, Finset.mem_insert_of_mem hebm⟩
  set F3 := F2.erase P.ebm with hF3
  have F3sub : ∀ f ∈ F3, f ∈ F ∧ f ≠ P.eam ∧ f ≠ P.ebm ∨ f = P.eab := by
    intro f hf
    simp only [F3, F2, F1, Finset.mem_erase, Finset.mem_insert] at hf
    obtain ⟨h1, h2, h3 | h3⟩ := hf
    · exact Or.inr h3
    · exact Or.inl ⟨h3, h2, h1⟩
  set K : Finset Pt := {P.m1, P.m2} with hK
  have eab_m1 : ¬ (P.eab.p = P.m1 ∨ P.eab.q = P.m1) := fun h => by
    rcases (P.hab.inc_iff _).1 h with h | h
    · exact P.m1a h
    · exact P.m1b h
  have eab_m2 : ¬ (P.eab.p = P.m2 ∨ P.eab.q = P.m2) := fun h => by
    rcases (P.hab.inc_iff _).1 h with h | h
    · exact P.m2a h
    · exact P.m2b h
  have closedK : Closed F3 K := by
    intro u hu w huw
    obtain ⟨f, hf, hfw⟩ := huw
    have hfu : f.p = u ∨ f.q = u := by
      rcases hfw with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact Or.inl h1
      · exact Or.inr h2
    have hfw' : f.p = w ∨ f.q = w := by
      rcases hfw with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact Or.inr h2
      · exact Or.inl h1
    have hfm : f = P.em := by
      simp only [K, Finset.mem_insert, Finset.mem_singleton] at hu
      rcases F3sub f hf with ⟨hfF, hne1, hne2⟩ | rfl
      · rcases hu with rfl | rfl
        · rcases at1 f hfF hfu with h | h
          · exact absurd h hne1
          · exact h
        · rcases at2 f hfF hfu with h | h
          · exact absurd h hne2
          · exact h
      · rcases hu with rfl | rfl
        · exact absurd hfu eab_m1
        · exact absurd hfu eab_m2
    subst hfm
    rcases (P.hm.inc_iff w).1 hfw' with rfl | rfl <;> simp [K]
  have m1K : P.m1 ∈ K := by simp [K]
  have m2K : P.m2 ∈ K := by simp [K]
  have notK : ∀ z, z ∉ K → ∀ w ∈ K, ¬ Conn F3 w z := fun z hz w hw h =>
    hz (closed_conn closedK hw h)
  have bK : P.b ∉ K := by simp [K, P.m1b.symm, P.m2b.symm]
  have t1K : P.t1 ∉ K := by simp [K, P.m1t1.symm, P.m2t1.symm]
  have e3 : ncomp V F2 + 1 = ncomp V F3 := by
    have := P.hbm.merge (V := V) (F := F3) hVb hVm2 (fun h => notK _ bK _ m2K h.symm)
    rwa [Finset.insert_erase hebmF2] at this
  have c3 : ∀ x y, x ∉ K → y ∉ K → (Conn F2 x y ↔ Conn F3 x y) := by
    intro x y hx hy
    rw [← Finset.insert_erase hebmF2, conn_insert]
    constructor
    · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact h
      · exfalso
        rcases P.hbm with ⟨q1, q2⟩ | ⟨q1, q2⟩
        · rw [q2] at h2; exact notK _ hy _ m2K h2
        · rw [q1] at h1; exact notK _ hx _ m2K h1.symm
      · exfalso
        rcases P.hbm with ⟨q1, q2⟩ | ⟨q1, q2⟩
        · rw [q2] at h1; exact notK _ hx _ m2K h1.symm
        · rw [q1] at h2; exact notK _ hy _ m2K h2
    · exact fun h => Or.inl h
  -- Step 4: insert `m1–t1` (merges `{m1, m2}` into `t1`'s class).
  set F4 := insert P.emt1 F3 with hF4
  have e4 : ncomp V F4 + 1 = ncomp V F3 :=
    P.hmt1.merge hVm1 hVt1 (fun h => notK _ t1K _ m1K h)
  have c4 : ∀ x y, x ∉ K → y ∉ K → (Conn F4 x y ↔ Conn F3 x y) := by
    intro x y hx hy
    rw [conn_insert]
    constructor
    · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact h
      · exfalso
        rcases P.hmt1 with ⟨q1, q2⟩ | ⟨q1, q2⟩
        · rw [q1] at h1; exact notK _ hx _ m1K h1.symm
        · rw [q2] at h2; exact notK _ hy _ m1K h2
      · exfalso
        rcases P.hmt1 with ⟨q1, q2⟩ | ⟨q1, q2⟩
        · rw [q1] at h2; exact notK _ hy _ m1K h2
        · rw [q2] at h1; exact notK _ hx _ m1K h1.symm
    · exact fun h => Or.inl h
  -- Membership facts in `F3`.
  have emF3 : P.em ∈ F3 := by
    simp only [F3, F2, F1, Finset.mem_erase, Finset.mem_insert]
    exact ⟨neq2.symm, neq1.symm, Or.inr hem⟩
  have et_ne_am : P.et ≠ P.eam := P.ht.ne_of P.ham P.m1t1 P.m1t2
  have et_ne_bm : P.et ≠ P.ebm := P.ht.ne_of P.hbm P.m2t1 P.m2t2
  have etF3 : P.et ∈ F3 := by
    simp only [F3, F2, F1, Finset.mem_erase, Finset.mem_insert]
    exact ⟨et_ne_bm, et_ne_am, Or.inr het⟩
  -- Step 5: insert `m2–t2` (inside a class).
  have s34 : F3 ⊆ F4 := Finset.subset_insert _ _
  have c45 : Conn F4 P.m2 P.t2 :=
    (((P.hm.conn (s34 emF3)).symm.trans (P.hmt1.conn (Finset.mem_insert_self _ _))).trans
      (P.ht.conn (s34 etF3)))
  set F5 := insert P.emt2 F4 with hF5
  have c5 : ∀ x y, Conn F5 x y ↔ Conn F4 x y := P.hmt2.insert_conn c45
  -- Step 6: erase `t1–t2` (still joined through `m1`, `m2`).
  have etF5 : P.et ∈ F5 := Finset.mem_insert_of_mem (s34 etF3)
  set F6 := F5.erase P.et with hF6
  have c56 : Conn F6 P.t1 P.t2 := by
    have a1 : P.emt1 ∈ F6 := Finset.mem_erase.2
      ⟨(P.ht.ne_of P.hmt1.swap P.m1t1 P.m1t2).symm,
        Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩
    have a2 : P.em ∈ F6 := Finset.mem_erase.2
      ⟨(P.ht.ne_of P.hm P.m2t1 P.m2t2).symm, Finset.mem_insert_of_mem (s34 emF3)⟩
    have a3 : P.emt2 ∈ F6 := Finset.mem_erase.2
      ⟨(P.ht.ne_of P.hmt2.swap P.m2t1 P.m2t2).symm, Finset.mem_insert_self _ _⟩
    exact ((P.hmt1.conn a1).symm.trans (P.hm.conn a2)).trans (P.hmt2.conn a3)
  have c6 : ∀ x y, Conn F6 x y ↔ Conn F5 x y := by
    intro x y
    have := P.ht.insert_conn c56 x y
    rw [Finset.insert_erase etF5] at this
    exact this.symm
  have hres : P.res F = F6 := rfl
  -- Assemble.
  have n1 : ncomp V F1 = ncomp V F := ncomp_congr (fun u _ v _ => c1 u v)
  have n2 : ncomp V F2 = ncomp V F1 := ncomp_congr (fun u _ v _ => c2 u v)
  have n5 : ncomp V F5 = ncomp V F4 := ncomp_congr (fun u _ v _ => c5 u v)
  have n6 : ncomp V F6 = ncomp V F5 := ncomp_congr (fun u _ v _ => c6 u v)
  refine ⟨by rw [hres]; omega, ?_⟩
  intro x y hx1 hx2 hy1 hy2
  have hx : x ∉ K := by simp [K, hx1, hx2]
  have hy : y ∉ K := by simp [K, hy1, hy2]
  rw [hres, c6, c5, c4 x y hx hy, ← c3 x y hx hy, c2, c1]
end APair
end ULHC
