-- Prove2me | solution 1 for Psi.muVec_tauOf_descent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:38:43.326215+00:00
-- url     : https://prove2.me/submissions/d15964a4-a9a4-4877-ae2b-1c51e46de9e1

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp
import Theorems.Thm_Psi_muVecAux_map_add
import Theorems.Thm_Psi_tauOf_descent


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution {w : List Bool} (hnd : noDescent w = false) (ha : ℕ)
    (av' : List ℕ) :
    muVec (tauOf w (ha :: av'))
      = ((cLead0 w + 1 + cLead1 (w.drop (cLead0 w))) + ha)
        :: muVecAux (tauOf ((w.drop (cLead0 w)).drop (cLead1 (w.drop (cLead0 w)) + 1)) av') ha := by
  rw [tauOf_descent hnd]
  simp only [muVec, muVecAux, Nat.sub_zero]
  rw [if_pos (by omega), List.singleton_append]
  congr 1
  rw [show cLead0 w + 1 + cLead1 (w.drop (cLead0 w)) + ha
        = ha + (cLead0 w + 1 + cLead1 (w.drop (cLead0 w))) from by omega, muVecAux_map_add]
end Psi
