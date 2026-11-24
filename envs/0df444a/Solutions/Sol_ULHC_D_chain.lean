-- Prove2me | solution 1 for ULHC.D_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:08:57.369723+00:00
-- url     : https://prove2.me/submissions/f52b9e65-83db-43c7-97c7-0bf97c2f6944

import Definitions.Def_ULHC_Arcs
import Definitions.Def_ULHC_D
import Theorems.Thm_ULHC_D_around
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge}
variable (hF : IsFactor V d F) (hH : IsFactor V d H)
include hF hH
namespace ULHC
theorem _root_.solution {a b : Pt} (h : Relation.ReflTransGen (MissAdj V) a b) :
    D F H a = D F H b := by
  induction h with
  | refl => rfl
  | @tail b' c' _ hbc ih =>
    obtain ⟨hb, hc, h1, h2⟩ := hbc
    let m : Pt := (max b'.1 c'.1 - 1, max b'.2 c'.2 - 1)
    have mb : Around b' m := by
      constructor <;> simp only [m] <;> rw [abs_le] at * <;> omega
    have mc : Around c' m := by
      constructor <;> simp only [m] <;> rw [abs_le] at * <;> omega
    rw [ih, ← D_around hF hH hb mb, D_around hF hH hc mc]
end ULHC
