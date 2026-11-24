-- Prove2me | solution 1 for Psi.tauOf_head_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:38:37.423976+00:00
-- url     : https://prove2.me/submissions/6bfce6d0-51d4-44b9-a6b8-3c67a147c255

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp
import Theorems.Thm_Psi_desComp_head_pos
import Theorems.Thm_Psi_deltaOf_cons
import Theorems.Thm_Psi_desComp_ne_nil


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (w : List Bool) (av : List ℕ) (hv : IsValid w av) :
    0 < (tauOf w av).headD 0 := by
  obtain ⟨hlen, -, -⟩ := hv
  obtain ⟨g0, gs, hg⟩ := List.exists_cons_of_ne_nil (desComp_ne_nil (false :: w))
  have hg0 : 0 < g0 := by
    have := desComp_head_pos (false :: w) (by simp)
    rw [hg] at this; simpa using this
  have hav : av ≠ [] := by
    intro h; subst h; rw [hg] at hlen; simp at hlen
  obtain ⟨a0, as, ha⟩ := List.exists_cons_of_ne_nil hav
  rw [tauOf, hg, deltaOf_cons, ha]
  simp only [List.zipWith_cons_cons, List.headD_cons]
  omega
end Psi
