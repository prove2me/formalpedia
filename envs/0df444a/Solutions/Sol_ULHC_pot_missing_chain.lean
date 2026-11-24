-- Prove2me | solution 1 for ULHC.pot_missing_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:27:44.399596+00:00
-- url     : https://prove2.me/submissions/5c0466f6-318c-4055-ab89-752a9b92caed

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Theorems.Thm_ULHC_pot_around_missing
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
variable {V : Finset Pt} {E : Finset Edge} {w : Edge → ℤ}
  (hS : Supp E w) (hb : Balanced w) (hE : ∀ e ∈ E, e.p ∈ V ∧ e.q ∈ V)
include hS hb hE
namespace ULHC
theorem _root_.solution {a b : Pt} (h : Relation.ReflTransGen (MissAdj V) a b) :
    pot E w a = pot E w b := by
  induction h with
  | refl => rfl
  | @tail b' c' _ hbc ih =>
    obtain ⟨hb', hc', h1, h2⟩ := hbc
    let m : Pt := (max b'.1 c'.1 - 1, max b'.2 c'.2 - 1)
    have mb : Around b' m := by
      constructor <;> simp only [m] <;> rw [abs_le] at * <;> omega
    have mc : Around c' m := by
      constructor <;> simp only [m] <;> rw [abs_le] at * <;> omega
    rw [ih, ← pot_around_missing hS hb hE hb' mb, pot_around_missing hS hb hE hc' mc]
end ULHC
