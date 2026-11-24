-- Prove2me | solution 1 for ULHC.ACell.merge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:13:33.183861+00:00
-- url     : https://prove2.me/submissions/8c5b2cab-d97d-4048-973e-da1930c6f3f9

import Definitions.Def_ULHC_Flip
import Definitions.Def_ULHC_AFlip
import Theorems.Thm_ULHC_Ends_conn
import Theorems.Thm_ULHC_Ends_insert_conn
import Theorems.Thm_ULHC_Ends_conn_insert_iff
import Theorems.Thm_ULHC_Ends_merge
import Theorems.Thm_ULHC_Ends_deg_erase
import Theorems.Thm_ULHC_Ends_erase_conn
import Theorems.Thm_ULHC_ACell_e2_ne_e1
import Theorems.Thm_ULHC_Adj_mono
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_mono
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_Inside_mono
import Theorems.Thm_ULHC_conn_insert
import Theorems.Thm_ULHC_deg_erase
import Theorems.Thm_ULHC_ncomp_congr


set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} (C : ACell)
  (hV : Inside V F) (hVa : C.a ∈ V) (hVb : C.b ∈ V) (hVd : C.d ∈ V) (hVk : C.k ∈ V)
  (he1 : C.e1 ∈ F) (he2 : C.e2 ∈ F) (hl1 : C.l1 ∉ F) (hl2 : C.l2 ∉ F)
  (hdeg2 : ∀ z, (Conn F C.a z ∨ Conn F C.d z) → deg F z = 2)
include hV hVa hVb hVd hVk he1 he2 hl1 hl2 hdeg2
omit hVb hVk hl1 hl2
namespace ULHC
namespace ACell
theorem _root_.solution (hn : ¬ Conn F C.a C.d) :
    ncomp V (C.res F) + 1 = ncomp V F ∧
      ∀ x y, Conn (C.res F) x y ↔
        Conn F x y ∨ (Conn F x C.a ∧ Conn F C.d y) ∨ (Conn F x C.d ∧ Conn F C.a y) := by
  set G1 := F.erase C.e1 with hG1
  have hG1F : G1 ⊆ F := Finset.erase_subset _ _
  have hab : Conn G1 C.a C.b :=
    C.h1.erase_conn hV he1 (fun z _ hz => by rw [hdeg2 z (Or.inl hz)]; exact even_two)
  have e1 : ncomp V G1 = ncomp V F := by
    conv_rhs => rw [← Finset.insert_erase he1]
    apply ncomp_congr; intro u _ v _; exact (C.h1.insert_conn hab u v).symm
  have he2' : C.e2 ∈ G1 := Finset.mem_erase.2 ⟨C.e2_ne_e1, he2⟩
  have hFab : Conn F C.a C.b := C.h1.conn he1
  have hdk : Conn (G1.erase C.e2) C.d C.k := by
    apply C.h2.erase_conn (hV.mono hG1F) he2'
    intro z _ hz
    have hzF : Conn F C.d z := hz.mono hG1F
    have hza : ¬ (z = C.a ∨ z = C.b) := by
      rintro (rfl | rfl)
      · exact hn hzF.symm
      · exact hn (hFab.trans hzF.symm)
    have := C.h1.deg_erase he1 z
    rw [if_neg hza, add_zero, ← hG1] at this
    rw [this, hdeg2 z (Or.inr hzF)]; exact even_two
  set G := G1.erase C.e2 with hG
  have hGF : G ⊆ F := (Finset.erase_subset _ _).trans hG1F
  have e2 : ncomp V G = ncomp V G1 := by
    conv_rhs => rw [← Finset.insert_erase he2']
    apply ncomp_congr; intro u _ v _; exact (C.h2.insert_conn hdk u v).symm
  have habG : Conn G C.a C.b := by
    have : Conn (insert C.e2 G) C.a C.b := by rw [Finset.insert_erase he2']; exact hab
    rcases conn_insert.1 this with h | ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h
    · have : Conn F C.a C.d ∨ Conn F C.a C.k := by
        rcases C.h2 with ⟨q1, _⟩ | ⟨q1, _⟩ <;> rw [q1] at h1
        · exact Or.inl (h1.mono hGF)
        · exact Or.inr (h1.mono hGF)
      rcases this with h | h
      · exact absurd h hn
      · exact absurd (h.trans (C.h2.conn he2).symm) hn
    · have : Conn F C.a C.d ∨ Conn F C.a C.k := by
        rcases C.h2 with ⟨_, q2⟩ | ⟨_, q2⟩ <;> rw [q2] at h1
        · exact Or.inr (h1.mono hGF)
        · exact Or.inl (h1.mono hGF)
      rcases this with h | h
      · exact absurd h hn
      · exact absurd (h.trans (C.h2.conn he2).symm) hn
  have em : ncomp V (insert C.l1 G) + 1 = ncomp V G :=
    C.h3.merge hVa hVd (fun h => hn (h.mono hGF))
  have hbk : Conn (insert C.l1 G) C.b C.k := by
    have s : G ⊆ insert C.l1 G := Finset.subset_insert _ _
    have hl' : Conn (insert C.l1 G) C.a C.d := C.h3.conn (Finset.mem_insert_self _ _)
    exact ((habG.mono s).symm.trans hl').trans (hdk.mono s)
  have er : ncomp V (C.res F) = ncomp V (insert C.l1 G) := by
    unfold ACell.res
    apply ncomp_congr; intro u _ v _; exact C.h4.insert_conn hbk u v
  refine ⟨by rw [er]; omega, fun x y => ?_⟩
  -- Connections: `G` has the same connections as `F`; then `l1` joins `a` and `d`.
  have cG1 : ∀ u v, Conn G1 u v ↔ Conn F u v := by
    intro u v
    have := C.h1.insert_conn hab u v
    rw [Finset.insert_erase he1] at this; exact this.symm
  have cG : ∀ u v, Conn G u v ↔ Conn G1 u v := by
    intro u v
    have := C.h2.insert_conn hdk u v
    rw [Finset.insert_erase he2'] at this
    exact this.symm
  have cGF : ∀ u v, Conn G u v ↔ Conn F u v := fun u v => (cG u v).trans (cG1 u v)
  unfold ACell.res
  rw [C.h4.insert_conn hbk, C.h3.conn_insert_iff, cGF, cGF, cGF, cGF, cGF]
end ACell
end ULHC
