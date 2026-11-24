-- Prove2me | solution 1 for ULHC.four_sides_class
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:44:23.142307+00:00
-- url     : https://prove2.me/submissions/e941ce1c-9f4e-44ca-9b21-13116761ce17

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
import Theorems.Thm_ULHC_corner_step
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Ends_ne_of
import Theorems.Thm_ULHC_Ends_swap
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_closed_conn
import Theorems.Thm_ULHC_ends_back
import Theorems.Thm_ULHC_ends_front
import Theorems.Thm_ULHC_ends_lat1
import Theorems.Thm_ULHC_ends_lat2
import Theorems.Thm_ULHC_isCell_corners
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} (hF : Deg2 V F) {g : Pt} (hg : IsCell V g)
    (tf : Side) (h1 : back g tf ∈ F) (h2 : front g tf ∈ F) (h3 : lat1 g tf ∈ F) (h4 : lat2 g tf ∈ F)
    {z : Pt} (hz : Conn F (back1 g tf) z) :
    z ∈ ({back1 g tf, back2 g tf, front1 g tf, front2 g tf} : Finset Pt) := by
  set K : Finset Pt := {back1 g tf, back2 g tf, front1 g tf, front2 g tf}
  obtain ⟨vb1, vb2, vf1, vf2⟩ := isCell_corners hg tf
  have eb := ends_back g tf; have ef := ends_front g tf
  have el1 := ends_lat1 g tf; have el2 := ends_lat2 g tf
  have mb1 : back1 g tf ∈ K := by simp [K]
  have mb2 : back2 g tf ∈ K := by simp [K]
  have mf1 : front1 g tf ∈ K := by simp [K]
  have mf2 : front2 g tf ∈ K := by simp [K]
  -- distinct sides
  have nq : ∀ (p q : Pt → Side → Pt), (∀ t', p g t' ≠ q g t') → p g tf ≠ q g tf := fun _ _ h => h tf
  have d1 : front1 g tf ≠ back1 g tf := by obtain ⟨x, y⟩ := g; cases tf <;> simp [back1, front1]
  have d2 : front1 g tf ≠ back2 g tf := by obtain ⟨x, y⟩ := g; cases tf <;> simp [back2, front1]
  have d3 : front2 g tf ≠ back1 g tf := by obtain ⟨x, y⟩ := g; cases tf <;> simp [back1, front2]
  have d4 : front2 g tf ≠ back2 g tf := by obtain ⟨x, y⟩ := g; cases tf <;> simp [back2, front2]
  have bf : back g tf ≠ lat1 g tf := eb.ne_of el1 d1 d2
  have bl2 : back g tf ≠ lat2 g tf := eb.ne_of el2 d3 d4
  have fl1 : front g tf ≠ lat1 g tf := ef.ne_of el1.swap d1.symm d3.symm
  have fl2 : front g tf ≠ lat2 g tf := ef.ne_of el2.swap d2.symm d4.symm
  have hK : Closed F K := by
    intro x hx y hxy
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact corner_step eb el1 h1 h3 bf (hF.2 _ vb1) (Or.inl rfl) (Or.inl rfl) ⟨mb1, mb2⟩
        ⟨mb1, mf1⟩ y hxy
    · exact corner_step eb el2 h1 h4 bl2 (hF.2 _ vb2) (Or.inr rfl) (Or.inl rfl) ⟨mb1, mb2⟩
        ⟨mb2, mf2⟩ y hxy
    · exact corner_step ef el1 h2 h3 fl1 (hF.2 _ vf1) (Or.inl rfl) (Or.inr rfl) ⟨mf1, mf2⟩
        ⟨mb1, mf1⟩ y hxy
    · exact corner_step ef el2 h2 h4 fl2 (hF.2 _ vf2) (Or.inr rfl) (Or.inr rfl) ⟨mf1, mf2⟩
        ⟨mb2, mf2⟩ y hxy
  exact closed_conn hK mb1 hz
end ULHC
