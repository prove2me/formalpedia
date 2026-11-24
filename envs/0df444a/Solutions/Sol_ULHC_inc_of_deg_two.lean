-- Prove2me | solution 1 for ULHC.inc_of_deg_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:11:53.540483+00:00
-- url     : https://prove2.me/submissions/d0cb1542-45dc-403c-95bf-fa2cc0b0c816

import Definitions.Def_ULHC_Flip
import Definitions.Def_ULHC_AFlip
import Theorems.Thm_ULHC_Ends_deg_erase
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_deg_erase
import Theorems.Thm_ULHC_one_le_deg


set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {F : Finset Edge} {z : Pt} (hd : deg F z = 2) {e e' f : Edge}
    (he : e ∈ F) (hz : e.p = z ∨ e.q = z) (he' : e' ∈ F) (hz' : e'.p = z ∨ e'.q = z)
    (hne : e ≠ e') (hf : f ∈ F) (hzf : f.p = z ∨ f.q = z) : f = e ∨ f = e' := by
  by_contra h
  push Not at h
  have h1 := ULHC.deg_erase he z
  rw [if_pos hz] at h1
  have he'' : e' ∈ F.erase e := Finset.mem_erase.2 ⟨hne.symm, he'⟩
  have h2 := ULHC.deg_erase he'' z
  rw [if_pos hz'] at h2
  have hf' : f ∈ (F.erase e).erase e' :=
    Finset.mem_erase.2 ⟨h.2, Finset.mem_erase.2 ⟨h.1, hf⟩⟩
  have h3 := one_le_deg hf' hzf
  omega
end ULHC
