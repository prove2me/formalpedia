-- Prove2me | solution 2 for ULHC.three_le_deg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:34:06.212805+00:00
-- url     : https://prove2.me/submissions/71d3f34b-6bff-4cd8-9e11-e3273ec275a6

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Stacked
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Ends_deg_erase
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_deg_erase
import Theorems.Thm_ULHC_one_le_deg


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {A : Finset Edge} {z : Pt} {g1 g2 g3 : Edge}
    (h1 : g1 ∈ A) (h2 : g2 ∈ A) (h3 : g3 ∈ A)
    (i1 : g1.p = z ∨ g1.q = z) (i2 : g2.p = z ∨ g2.q = z) (i3 : g3.p = z ∨ g3.q = z)
    (n12 : g1 ≠ g2) (n13 : g1 ≠ g3) (n23 : g2 ≠ g3) : 3 ≤ deg A z := by
  have e1 := deg_erase h1 z
  rw [if_pos i1] at e1
  have h2' : g2 ∈ A.erase g1 := Finset.mem_erase.2 ⟨n12.symm, h2⟩
  have e2 := deg_erase h2' z
  rw [if_pos i2] at e2
  have h3' : g3 ∈ (A.erase g1).erase g2 :=
    Finset.mem_erase.2 ⟨n23.symm, Finset.mem_erase.2 ⟨n13.symm, h3⟩⟩
  have := one_le_deg h3' i3
  omega
end ULHC
