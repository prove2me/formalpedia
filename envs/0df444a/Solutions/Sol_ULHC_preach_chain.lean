-- Prove2me | solution 1 for ULHC.preach_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:28:55.024437+00:00
-- url     : https://prove2.me/submissions/b7747ef2-62c7-4934-9355-c9f910048e17

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Theorems.Thm_ULHC_crossL_append
import Theorems.Thm_ULHC_isChain_append
import Theorems.Thm_ULHC_Conn_refl
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} (B : Finset Edge)
namespace ULHC
theorem _root_.solution {a c : Pt} {b b' : Bool}
    (h : Relation.ReflTransGen (PStep V B) (a, b) (c, b')) :
    ∃ l, List.IsChain (Adj (GE V)) (a :: l) ∧ (a :: l).getLast (by simp) = c ∧
      (crossL B a l % 2 = if b = b' then 0 else 1) := by
  generalize hx : ((a, b) : Pt × Bool) = x at h
  generalize hy : ((c, b') : Pt × Bool) = y at h
  induction h generalizing c b' with
  | refl =>
    subst hx; simp only [Prod.mk.injEq] at hy; obtain ⟨rfl, rfl⟩ := hy
    exact ⟨[], List.IsChain.singleton _, rfl, by simp [crossL]⟩
  | @tail y' z _ hyz ih =>
    subst hx hy
    obtain ⟨l, hl, hlast, hpar⟩ := ih rfl
    obtain ⟨h1, h2⟩ := hyz
    refine ⟨l ++ [c], isChain_append hl (by rw [hlast]; exact h1), by simp, ?_⟩
    rw [crossL_append, hlast]
    simp only at h2
    rw [h2]
    have key : ∀ (X : ℕ) (b c tf : Bool), X % 2 = (if b = c then 0 else 1) →
        (X + (if tf = true then 1 else 0)) % 2 = (if b = (c ^^ tf) then 0 else 1) := by
      intro X b c tf h
      cases b <;> cases c <;> cases tf <;> simp at h ⊢ <;> omega
    have := key (crossL B a l) b y'.2 (decide (∃ e ∈ B, Ends e y'.1 c)) hpar
    simpa only [decide_eq_true_eq] using this
end ULHC
