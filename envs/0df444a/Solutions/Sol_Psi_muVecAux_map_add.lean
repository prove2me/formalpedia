-- Prove2me | solution 1 for Psi.muVecAux_map_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:36:23.189813+00:00
-- url     : https://prove2.me/submissions/1fabc06d-779e-4315-84a4-a309c739be8a

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (M : List ℕ) (q c : ℕ) :
    muVecAux (M.map (· + c)) (q + c) = muVecAux M q := by
  induction M generalizing q with
  | nil => simp [muVecAux]
  | cons x xs ih =>
    simp only [List.map_cons, muVecAux]
    rw [show x + c - (q + c) = x - q from by omega, ih x]
end Psi
