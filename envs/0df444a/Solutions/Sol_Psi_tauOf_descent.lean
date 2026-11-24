-- Prove2me | solution 1 for Psi.tauOf_descent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:36:37.562098+00:00
-- url     : https://prove2.me/submissions/a891a83c-0f35-4498-a46c-a383a010b87e

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
import Theorems.Thm_Psi_deltaOf_cons
import Theorems.Thm_Psi_desComp_descent
import Theorems.Thm_Psi_zipWith_add_map

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution {w : List Bool} (hnd : noDescent w = false) (ha : ℕ) (av' : List ℕ) :
    tauOf w (ha :: av') =
      ((cLead0 w + 1 + cLead1 (w.drop (cLead0 w))) + ha)
        :: (tauOf ((w.drop (cLead0 w)).drop (cLead1 (w.drop (cLead0 w)) + 1)) av').map
            (· + (cLead0 w + 1 + cLead1 (w.drop (cLead0 w)))) := by
  unfold tauOf
  rw [desComp_descent hnd, deltaOf_cons]
  simp only [List.zipWith_cons_cons]
  rw [zipWith_add_map]
end Psi
