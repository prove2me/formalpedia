-- Prove2me | solution 1 for VpVnp.separation
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:55:01.83831+00:00
-- url     : https://prove2.me/submissions/0083c11d-f137-41ab-9e72-015863276a1c

import Theorems.Thm_ValiantBorder_separation
import Mathlib
import Definitions.Def_VpVnp_Circuit
import Definitions.Def_VpVnp_Approximates
import Definitions.Def_VpVnp_Classes

universe u

open VpVnp

theorem solution : ∀ (F : Type u) [Field F], VP F ⊂ VNP F := by
  intro F inst
  have h := ValiantBorder.separation F
  constructor
  · intro f hf
    let g : Statement.Family F := { vars := f.vars, fin := f.fin, poly := f.poly }
    exact h.1 (show g ∈ Statement.VP F from hf)
  · intro hrev
    apply h.2
    intro g hg
    let f : VpVnp.Family F := { vars := g.vars, fin := g.fin, poly := g.poly }
    exact hrev (show f ∈ VpVnp.VNP F from hg)
