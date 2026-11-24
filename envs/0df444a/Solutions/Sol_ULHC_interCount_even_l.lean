-- Prove2me | solution 1 for ULHC.interCount_even_l
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:16:28.409743+00:00
-- url     : https://prove2.me/submissions/5afcd2f5-e4a4-4526-b128-774ed6e318fa

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Theorems.Thm_ULHC_inter_local
import Theorems.Thm_ULHC_inter_dark_lat_l
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Ends_conn
import Theorems.Thm_ULHC_Ends_conn_iff
import Theorems.Thm_ULHC_GridIso_conn_iff
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} (hF : Deg2 V F)
include hF
namespace ULHC
theorem _root_.solution {w : Pt} (hw : IsCell V w) (hTw : NotTypeIII V F w)
    (hTn : ∀ s, Inter V F (sideEdge w s) → IsCell V (nb w s) → NotTypeIII V F (nb w s)) :
    interCount V F w % 2 = 0 := by
  obtain ⟨x, y⟩ := w
  have hw' := hw
  obtain ⟨va, vb, vd, vk⟩ := hw
  set a : Pt := (x, y)
  set b : Pt := (x + 1, y)
  set d : Pt := (x, y + 1)
  set k : Pt := (x + 1, y + 1)
  have key := inter_local (decide (bot (x, y) ∈ F)) (decide (top (x, y) ∈ F))
    (decide (lft (x, y) ∈ F)) (decide (rgt (x, y) ∈ F))
    (decide (Conn F a b)) (decide (Conn F a d)) (decide (Conn F a k)) (decide (Conn F b d))
    (decide (Conn F b k)) (decide (Conn F d k))
  -- Transitivity of the corner relation.
  have tri : triOK (decide (Conn F a b)) (decide (Conn F a d)) (decide (Conn F a k))
      (decide (Conn F b d)) (decide (Conn F b k)) (decide (Conn F d k)) = true := by
    unfold triOK
    simp only [Bool.and_eq_true, Bool.le_iff_imp, decide_eq_true_eq]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;>
      intro h <;> obtain ⟨h1, h2⟩ := h
    all_goals first
      | exact h1.trans h2 | exact h1.trans h2.symm | exact h1.symm.trans h2
  have dk1 : ∀ (e : Edge) (u v : Pt), Ends e u v → (decide (e ∈ F) ≤ decide (Conn F u v)) := by
    intro e u v he
    simp only [Bool.le_iff_imp, decide_eq_true_eq]
    exact fun h => he.conn h
  have eb : Ends (bot (x, y)) a b := Or.inl ⟨rfl, rfl⟩
  have et : Ends (top (x, y)) d k := Or.inl ⟨rfl, rfl⟩
  have el : Ends (lft (x, y)) a d := Or.inl ⟨rfl, rfl⟩
  have er : Ends (rgt (x, y)) b k := Or.inl ⟨rfl, rfl⟩
  -- No Type III cell.
  have t1 : (decide (bot (x, y) ∈ F) && decide (top (x, y) ∈ F) && !decide (lft (x, y) ∈ F) &&
      !decide (rgt (x, y) ∈ F)) ≤ decide (Conn F a d) := by
    simp only [Bool.le_iff_imp, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not]
    rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    have := hTw .t h1 h2 h3 h4
    simpa [back1, front1] using this
  have t2 : (decide (lft (x, y) ∈ F) && decide (rgt (x, y) ∈ F) && !decide (bot (x, y) ∈ F) &&
      !decide (top (x, y) ∈ F)) ≤ decide (Conn F a b) := by
    simp only [Bool.le_iff_imp, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not]
    rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    have := hTw .r h1 h2 h3 h4
    simpa [back1, front1] using this
  -- Inter sides have a dark neighbour.
  have iE : ∀ s : Side, IsEdge V (sideEdge (x, y) s) := by
    intro s; cases s <;> simp [IsEdge, sideEdge, bot, top, lft, rgt, Edge.q] <;>
      exact ⟨by assumption, by assumption⟩
  have nl : ∀ (s : Side) (u v : Pt), Ends (sideEdge (x, y) s) u v →
      ((!decide (sideEdge (x, y) s ∈ F) && !decide (Conn F u v)) ≤
        (decide (sideEdge (x, y) (latA s) ∈ F) || decide (sideEdge (x, y) (latB s) ∈ F))) := by
    intro s u v he
    simp only [Bool.le_iff_imp, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      Bool.or_eq_true, decide_eq_true_eq]
    rintro ⟨h1, h2⟩
    have hI : Inter V F (sideEdge (x, y) s) := ⟨iE s, h1, fun h => h2 ((he.conn_iff F).1 h)⟩
    exact inter_dark_lat_l hF hw' s hI (hTn s hI)
  have hcount := key tri (dk1 _ _ _ eb) (dk1 _ _ _ et) (dk1 _ _ _ el) (dk1 _ _ _ er) t1 t2
    (nl .b a b eb) (nl .t d k et) (nl .l a d el) (nl .r b k er)
  -- Translate back.
  have tr : ∀ (e : Edge) (u v : Pt), Ends e u v → IsEdge V e →
      bI (!decide (e ∈ F) && !decide (Conn F u v)) = if Inter V F e then 1 else 0 := by
    intro e u v he hE
    unfold Inter
    rw [he.conn_iff]
    by_cases h1 : e ∈ F <;> by_cases h2 : Conn F u v <;> simp [bI, h1, h2, hE]
  unfold interCount
  rw [← tr _ _ _ eb (iE .b), ← tr _ _ _ et (iE .t), ← tr _ _ _ el (iE .l), ← tr _ _ _ er (iE .r)]
  exact hcount
end ULHC
