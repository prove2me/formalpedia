-- Prove2me | solution 1 for ULHC.three_le_deg
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T03:35:50.456817+00:00
-- url     : https://prove2.me/submissions/1f86049c-1fee-4f99-bf36-6387a3cf0a4a

import Definitions.Def_ULHC_Grid
open ULHC
private theorem incident_cases (e : Edge) (z : Pt) (h : e.p = z ∨ e.q = z) :
    e = eR z ∨ e = eL z ∨ e = eU z ∨ e = eD z := by
  rcases e with ⟨d,⟨a,b⟩⟩; cases d <;> rcases h with h | h <;> subst z <;>
    simp [Edge.q,eR,eL,eU,eD]




theorem solution {A : Finset Edge} {z : Pt} {g1 g2 g3 : Edge}
    (h1 : g1 ∈ A) (h2 : g2 ∈ A) (h3 : g3 ∈ A)
    (i1 : g1.p = z ∨ g1.q = z) (i2 : g2.p = z ∨ g2.q = z) (i3 : g3.p = z ∨ g3.q = z)
    (n12 : g1 ≠ g2) (n13 : g1 ≠ g3) (n23 : g2 ≠ g3) : 3 ≤ deg A z := by
  rcases incident_cases g1 z i1 with rfl|rfl|rfl|rfl <;>
    rcases incident_cases g2 z i2 with rfl|rfl|rfl|rfl <;>
    rcases incident_cases g3 z i3 with rfl|rfl|rfl|rfl <;>
    first | contradiction | (simp [deg,ind,h1,h2,h3] <;> split <;> decide)
