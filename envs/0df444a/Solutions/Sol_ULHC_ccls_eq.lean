-- Prove2me | solution 1 for ULHC.ccls_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:54:32.196413+00:00
-- url     : https://prove2.me/submissions/b4956858-8f14-49cc-8807-f51b75608a31

import Definitions.Def_ULHC_TwoFactor
import Definitions.Def_ULHC_Comp
import Theorems.Thm_ULHC_mem_fnbr
import Theorems.Thm_ULHC_creach_succ
import Theorems.Thm_ULHC_creach_mono
import Theorems.Thm_ULHC_creach_conn
import Theorems.Thm_ULHC_creach_sub
import Theorems.Thm_ULHC_creach_stable
import Theorems.Thm_ULHC_creach_fix
import Theorems.Thm_ULHC_Conn_refl
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_adj_inc
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge}
namespace ULHC
theorem _root_.solution (hFV : Inside V F) {x : Pt} (hx : x ∈ V) : ccls V F x = cls V F x := by
  classical
  obtain ⟨k, hk, hfix⟩ := creach_fix hFV hx
  have hst : creach F x V.card = creach F x k := creach_stable hfix _ hk
  have closed : ∀ u ∈ creach F x k, ∀ v, Adj F u v → v ∈ creach F x k := by
    intro u hu v huv
    obtain ⟨e, he, hi, _, rfl⟩ := adj_inc huv
    rw [← hfix, creach_succ, mem_union, mem_biUnion]
    exact Or.inr ⟨u, hu, mem_fnbr.2 ⟨e, he, hi, rfl⟩⟩
  ext z
  unfold ccls cls
  rw [mem_filter, hst]
  constructor
  · intro hz
    exact ⟨creach_sub hFV hx k hz, creach_conn k z hz⟩
  · rintro ⟨-, hc⟩
    induction hc with
    | refl => exact creach_mono (Nat.zero_le k) (by simp [creach])
    | tail _ hbc ih => exact closed _ ih _ hbc
end ULHC
