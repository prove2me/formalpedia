-- Prove2me | solution 1 for Psi.deltaAux_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:34:08.102391+00:00
-- url     : https://prove2.me/submissions/ae9cab17-5e34-47e8-b36d-e614e804ab88

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (γ : List ℕ) (acc : ℕ) : (deltaAux γ acc).length = γ.length := by
  induction γ generalizing acc with
  | nil => simp [deltaAux]
  | cons x xs ih => simp only [deltaAux, List.length_cons]; rw [ih]
end Psi
