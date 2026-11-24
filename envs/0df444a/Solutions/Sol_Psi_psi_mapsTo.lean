-- Prove2me | solution 1 for Psi.psi_mapsTo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:59:46.290519+00:00
-- url     : https://prove2.me/submissions/ca780023-a925-43a3-baaf-0a97b1fd3c63

import Definitions.Def_RequestProject_Psi_Inverse
import Definitions.Def_RequestProject_Psi_Bijection
import Theorems.Thm_Psi_psi_isValid
import Theorems.Thm_Psi_phi_psi
import Theorems.Thm_Psi_phi_size


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) :
    Set.MapsTo psiPath (Cod n) (Dom n) := by
  rintro π ⟨hd, hsize⟩
  have hne : π ≠ [] := by rintro rfl; simp only [List.length_nil] at hsize; omega
  refine ⟨?_, psi_isValid π hd hne⟩
  have hround := phi_psi π hd hne
  have hs := phi_size (psiPath π).1 (psiPath π).2
  rw [hround, hsize] at hs
  omega
end Psi
