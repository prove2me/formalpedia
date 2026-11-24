-- Prove2me | solution 1 for Psi.isValid_av_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:36:54.309907+00:00
-- url     : https://prove2.me/submissions/03b46ae3-6b52-4c84-8f89-8738740e5551

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
import Theorems.Thm_Psi_desComp_descent

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (w : List Bool) (av : List ℕ) (hv : IsValid w av)
    (hnd : noDescent w = false) : av = av.headD 0 :: av.tail := by
  obtain ⟨hlen, _, _⟩ := hv
  cases av with
  | nil => rw [desComp_descent hnd] at hlen; simp at hlen
  | cons x xs => rfl
end Psi
