-- Prove2me | solution 1 for Psi.desComp_head_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:37:05.782592+00:00
-- url     : https://prove2.me/submissions/04e82b6e-8af3-4c2a-afd9-f528acd11299

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (word : List Bool) (hw : word ≠ []) :
    0 < (desComp word).headD 0 := by
  have gen : ∀ (word : List Bool) (cur : ℕ), word ≠ [] → 0 < (desCompAux word cur).headD 0 := by
    intro word
    induction word with
    | nil => intro cur h; exact absurd rfl h
    | cons a t iht =>
      intro cur _
      cases t with
      | nil => simp [desCompAux]
      | cons b rest =>
        simp only [desCompAux]
        split
        · simp
        · exact iht (cur + 1) (by simp)
  exact gen word 0 hw
end Psi
