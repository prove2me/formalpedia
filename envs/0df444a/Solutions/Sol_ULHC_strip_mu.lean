-- Prove2me | solution 1 for ULHC.strip_mu
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:27:01.308089+00:00
-- url     : https://prove2.me/submissions/0d8cc6d1-36c0-4cd8-b848-0990e0dd965a

import Definitions.Def_ULHC_Phase
import Definitions.Def_ULHC_Phase2
import Theorems.Thm_ULHC_end_arcs
import Theorems.Thm_ULHC_pat_flip_end
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_D_flip_sink
import Theorems.Thm_ULHC_D_flip_source
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_flipCol_succ
import Theorems.Thm_ULHC_mu_flip_sink
import Theorems.Thm_ULHC_mu_flip_source
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {V : Finset Pt} {F H : Finset Edge} {c : Pt} {s : Side} {o : Bool}
    (hp : ParOK c s o) :
    ∀ n, StripPat F c s n → (∀ j < n, IsCell V (cellJ c s j)) →
      (∀ j < n, Good o (D F H (cellJ c s j))) →
      mu V (flipCol F c s n) H + 2 * n = mu V F H := by
  intro n
  induction n generalizing F with
  | zero => intro _ _ _; simp [flipCol]
  | succ n ih =>
    intro hpat hcell hgood
    rw [flipCol_succ]
    have hce : IsCell V (cellJ c s n) := hcell n (by omega)
    have arcs := end_arcs hp hpat
    have hge : Good o (D F H (cellJ c s n)) := hgood n (by omega)
    -- The last cell is improving.
    have hstep : mu V (flip F (cellJ c s n)) H + 2 = mu V F H := by
      cases o
      · exact mu_flip_source hce (fun s' => by simpa using arcs s')
          (by unfold Good at hge; simp at hge; omega)
      · exact mu_flip_sink hce (fun s' => by simpa using arcs s')
          (by unfold Good at hge; simp at hge; omega)
    have hD : ∀ j < n, D (flip F (cellJ c s n)) H (cellJ c s j) = D F H (cellJ c s j) := by
      intro j hj
      have hne : cellJ c s j ≠ cellJ c s n := by
        obtain ⟨x, y⟩ := c; cases s <;> simp [cellJ] <;> omega
      cases o
      · rw [D_flip_source (fun s' => by simpa using arcs s')]; simp [hne]
      · rw [D_flip_sink (fun s' => by simpa using arcs s')]; simp [hne]
    rcases n with _ | n
    · simp [flipCol]; omega
    · have := ih (pat_flip_end hpat) (fun j hj => hcell j (by omega))
        (fun j hj => by rw [hD j hj]; exact hgood j (by omega))
      omega
end ULHC
