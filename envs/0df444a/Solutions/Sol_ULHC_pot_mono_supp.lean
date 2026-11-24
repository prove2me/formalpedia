-- Prove2me | solution 1 for ULHC.pot_mono_supp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:59:45.372621+00:00
-- url     : https://prove2.me/submissions/de37f010-881f-44e9-8843-02e5e06611ed

import Definitions.Def_ULHC_Grid
import Definitions.Def_ULHC_Potential
import Theorems.Thm_ULHC_pot_eq_sum_ite
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable {E : Finset Edge} {w : Edge → ℤ}
namespace ULHC
theorem _root_.solution {E E' : Finset Edge} (hsub : E ⊆ E') (hS : Supp E w) (c : Pt) :
    pot E w c = pot E' w c := by
  rw [pot_eq_sum_ite, pot_eq_sum_ite]
  apply Finset.sum_subset hsub
  intro e _ he
  rw [hS e he]; simp
end ULHC
