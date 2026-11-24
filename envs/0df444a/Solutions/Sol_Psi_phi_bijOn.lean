-- Prove2me | solution 1 for Psi.phi_bijOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:02:03.925549+00:00
-- url     : https://prove2.me/submissions/a99ffa39-8af0-4670-a9f4-335bc2587a92

import Definitions.Def_RequestProject_Psi_Inverse
import Definitions.Def_RequestProject_Psi_Bijection
import Theorems.Thm_Psi_psi_mapsTo
import Theorems.Thm_Psi_phi_mapsTo
import Theorems.Thm_Psi_phi_psi
import Theorems.Thm_Psi_psi_phi


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) :
    Set.BijOn (fun p : List Bool × List ℕ => phiPath p.1 p.2) (Dom n) (Cod n) := by
  refine Set.InvOn.bijOn ⟨?_, ?_⟩ (phi_mapsTo n) (psi_mapsTo n hn)
  · rintro ⟨w, av⟩ ⟨_, hv⟩
    exact psi_phi w av hv
  · intro π hπ
    refine phi_psi π hπ.1 ?_
    intro hnil; rw [hnil] at hπ; simp only [Cod, Set.mem_setOf_eq, List.length_nil] at hπ; omega
end Psi
