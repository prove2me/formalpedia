-- Prove2me | solution 1 for Psi.isValid_base_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:36:12.567803+00:00
-- url     : https://prove2.me/submissions/5d45defa-eef7-41be-8f68-4a83ad543c7c

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
import Theorems.Thm_Psi_desComp_noDescent

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (w : List Bool) (av : List ℕ) (hv : IsValid w av)
    (hnd : noDescent w = true) : av.sum = 0 := by
  obtain ⟨hlen, _, hlast⟩ := hv
  rw [desComp_noDescent hnd, List.length_singleton] at hlen
  cases av with
  | nil => simp at hlen
  | cons c t =>
    cases t with
    | cons _ _ => simp at hlen
    | nil =>
      rw [tauOf, desComp_noDescent hnd] at hlast
      simp only [deltaOf, deltaAux, List.zipWith_cons_cons,
        List.zipWith_nil_right, List.getLast?_singleton, Option.some.injEq] at hlast
      simp only [List.sum_cons, List.sum_nil, add_zero]
      omega
end Psi
