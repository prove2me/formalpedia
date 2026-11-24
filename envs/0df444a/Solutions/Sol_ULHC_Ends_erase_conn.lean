-- Prove2me | solution 1 for ULHC.Ends.erase_conn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:11:51.621313+00:00
-- url     : https://prove2.me/submissions/09b7c556-b97e-4345-bb08-9bcf988caabd

import Definitions.Def_ULHC_Flip
import Definitions.Def_ULHC_AFlip
import Theorems.Thm_ULHC_Ends_conn_iff
import Theorems.Thm_ULHC_Ends_conn
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_conn_erase_of_even


set_option autoImplicit true
open ULHC
open Finset Classical
variable {e : Edge} {u v : Pt}
namespace ULHC
namespace Ends
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} (hV : Inside V F) (h : Ends e u v)
    (he : e ∈ F) (heven : ∀ z ∈ V, Conn F u z → Even (deg F z)) : Conn (F.erase e) u v := by
  have huv : Conn F u v := h.conn he
  have := conn_erase_of_even hV he (by
    intro z hz hc
    apply heven z hz
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
    · rwa [h1] at hc
    · rw [h1] at hc; exact huv.trans hc)
  exact (h.conn_iff _).1 this
end Ends
end ULHC
