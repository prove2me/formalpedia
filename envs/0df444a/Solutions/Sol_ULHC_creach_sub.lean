-- Prove2me | solution 1 for ULHC.creach_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:51:46.258796+00:00
-- url     : https://prove2.me/submissions/c907b850-e03c-48a5-b9fb-0bf4c04ae4eb

import Definitions.Def_ULHC_TwoFactor
import Definitions.Def_ULHC_Comp
import Theorems.Thm_ULHC_creach_conn
import Theorems.Thm_ULHC_conn_mem


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge}
namespace ULHC
theorem _root_.solution (hFV : Inside V F) {x : Pt} (hx : x ∈ V) : ∀ k, creach F x k ⊆ V := by
  intro k z hz
  exact conn_mem hFV hx (creach_conn k z hz)
end ULHC
