-- Prove2me | solution 1 for Psi.phi_mapsTo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:39:06.571799+00:00
-- url     : https://prove2.me/submissions/9df0ae4e-673d-4626-a8ec-8fe30b104e9c

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward
import Theorems.Thm_Psi_phi_isDyck
import Theorems.Thm_Psi_phi_size


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (n : ℕ) :
    Set.MapsTo (fun p : List Bool × List ℕ => phiPath p.1 p.2) (Dom n) (Cod n) := by
  rintro ⟨w, av⟩ ⟨hlen, _⟩
  refine ⟨phi_isDyck w av, ?_⟩
  rw [phi_size]; omega
end Psi
