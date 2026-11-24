-- Prove2me | solution 1 for Psi.desCompAux_ne_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:34:36.370956+00:00
-- url     : https://prove2.me/submissions/1e008f63-b10b-41c1-a98e-65b46d306c19

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (word : List Bool) (cur : ℕ) : desCompAux word cur ≠ [] := by
  induction word generalizing cur with
  | nil => simp [desCompAux]
  | cons a t iht =>
    cases t with
    | nil => simp [desCompAux]
    | cons b rest =>
      simp only [desCompAux]
      split
      · simp
      · exact iht (cur + 1)
end Psi
