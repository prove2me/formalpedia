-- Prove2me | solution 1 for Psi.deltaOf_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:33:12.762809+00:00
-- url     : https://prove2.me/submissions/30a9608f-a9b2-456c-8d2c-6bdf8af6f09a

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
import Theorems.Thm_Psi_deltaAux_shift

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (x : ℕ) (r : List ℕ) :
    deltaOf (x :: r) = x :: (deltaOf r).map (· + x) := by
  simp only [deltaOf, deltaAux, zero_add]; rw [deltaAux_shift r x]
end Psi
