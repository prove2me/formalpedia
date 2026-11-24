-- Prove2me | solution 1 for Psi.isValid_zeros
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:48:53.582842+00:00
-- url     : https://prove2.me/submissions/12e6c746-7cdf-4761-ac08-53afbcf8a869

import Definitions.Def_RequestProject_Psi_Inverse
import Definitions.Def_RequestProject_Psi_Bijection
import Theorems.Thm_Psi_desComp_noDescent
import Theorems.Thm_Psi_noDescent_sorted


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (a : ℕ) : IsValid (List.replicate a false) [0] := by
  have hnd : noDescent (List.replicate a false) = true := by simpa using noDescent_sorted a 0
  refine ⟨?_, ?_, ?_⟩
  · rw [desComp_noDescent hnd]; simp
  · rw [tauOf, desComp_noDescent hnd]; simp [deltaOf, deltaAux]
  · rw [tauOf, desComp_noDescent hnd]; simp [deltaOf, deltaAux, List.length_replicate]
end Psi
