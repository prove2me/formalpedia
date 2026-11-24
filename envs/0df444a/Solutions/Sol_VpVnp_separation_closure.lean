-- Prove2me | solution 1 for VpVnp.separation_closure
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:55:03.034269+00:00
-- url     : https://prove2.me/submissions/7a953f2d-73b0-499a-a2fe-7740b1b50dc9

import Theorems.Thm_ValiantBorder_allFields
import Mathlib
import Definitions.Def_VpVnp_Circuit
import Definitions.Def_VpVnp_Approximates
import Definitions.Def_VpVnp_Classes

universe u

open VpVnp

theorem solution : ∀ (F : Type u) [Field F], ¬ VNP F ⊆ VPBar F := by
  intro F inst h
  apply ValiantBorder.allFields.2 F
  intro g hg
  let f : VpVnp.Family F := { vars := g.vars, fin := g.fin, poly := g.poly }
  exact h (show f ∈ VpVnp.VNP F from hg)
