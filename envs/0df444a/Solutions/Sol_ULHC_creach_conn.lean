-- Prove2me | solution 1 for ULHC.creach_conn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:49:53.067937+00:00
-- url     : https://prove2.me/submissions/09df8ea3-b667-4c29-9820-34792b771075

import Definitions.Def_ULHC_TwoFactor
import Definitions.Def_ULHC_Comp
import Theorems.Thm_ULHC_mem_fnbr
import Theorems.Thm_ULHC_creach_succ
import Theorems.Thm_ULHC_Conn_of_adj
import Theorems.Thm_ULHC_Conn_refl
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_adj_other


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge}
namespace ULHC
theorem _root_.solution {x : Pt} : ∀ k, ∀ z ∈ creach F x k, Conn F x z := by
  intro k
  induction k with
  | zero => intro z hz; rw [creach, mem_singleton] at hz; rw [hz]; exact Conn.refl F x
  | succ k ih =>
    intro z hz
    rw [creach_succ, mem_union, mem_biUnion] at hz
    rcases hz with hz | ⟨u, hu, hz⟩
    · exact ih z hz
    · obtain ⟨e, he, hi, rfl⟩ := mem_fnbr.1 hz
      exact (ih u hu).trans (Conn.of_adj (adj_other he hi))
end ULHC
