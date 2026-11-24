-- Prove2me | solution 1 for Psi.isValid_zeros_ones
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:49:03.699107+00:00
-- url     : https://prove2.me/submissions/ab94934c-df44-4ac7-90fe-e9cc790c0647

import Definitions.Def_RequestProject_Psi_Inverse
import Definitions.Def_RequestProject_Psi_Bijection
import Theorems.Thm_Psi_desComp_noDescent
import Theorems.Thm_Psi_noDescent_sorted


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (a b : ℕ) :
    IsValid (List.replicate a false ++ List.replicate b true) [0] := by
  have hnd : noDescent (List.replicate a false ++ List.replicate b true) = true :=
    noDescent_sorted a b
  refine ⟨?_, ?_, ?_⟩
  · rw [desComp_noDescent hnd]; simp
  · rw [tauOf, desComp_noDescent hnd]; simp [deltaOf, deltaAux]
  · rw [tauOf, desComp_noDescent hnd]
    simp [deltaOf, deltaAux, List.length_append, List.length_replicate]
end Psi
