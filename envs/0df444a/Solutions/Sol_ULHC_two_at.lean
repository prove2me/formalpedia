-- Prove2me | solution 1 for ULHC.two_at
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T03:36:01.450551+00:00
-- url     : https://prove2.me/submissions/643e6ed0-ac99-407a-9970-b0dfdd77f262

import Definitions.Def_ULHC_Grid
open ULHC
private theorem incident_cases (e : Edge) (z : Pt) (h : e.p = z ∨ e.q = z) :
    e = eR z ∨ e = eL z ∨ e = eU z ∨ e = eD z := by
  rcases e with ⟨d,⟨a,b⟩⟩; cases d <;> rcases h with h | h <;> subst z <;>
    simp [Edge.q,eR,eL,eU,eD]

private theorem three_bound {A : Finset Edge} {z : Pt} {a b c : Edge}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (ia : a.p = z ∨ a.q = z) (ib : b.p = z ∨ b.q = z) (ic : c.p = z ∨ c.q = z)
    (nab : a ≠ b) (nac : a ≠ c) (nbc : b ≠ c) : 3 ≤ deg A z := by
  rcases incident_cases a z ia with rfl|rfl|rfl|rfl <;>
    rcases incident_cases b z ib with rfl|rfl|rfl|rfl <;>
    rcases incident_cases c z ic with rfl|rfl|rfl|rfl <;>
    first | contradiction | (simp [deg,ind,ha,hb,hc] <;> split <;> decide)



theorem solution {A : Finset Edge} {p : Pt} {g1 g2 x : Edge} (hdeg : deg A p = 2) (h1 : g1 ∈ A)
    (h2 : g2 ∈ A) (i1 : g1.p = p ∨ g1.q = p) (i2 : g2.p = p ∨ g2.q = p) (n12 : g1 ≠ g2)
    (hx : x ∈ A) (ix : x.p = p ∨ x.q = p) : x = g1 ∨ x = g2 := by
  by_contra! H; have H3 := three_bound h1 h2 hx i1 i2 ix n12 (Ne.symm H.1) (Ne.symm H.2); omega
