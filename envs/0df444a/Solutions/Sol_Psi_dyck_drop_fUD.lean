-- Prove2me | solution 1 for Psi.dyck_drop_fUD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:44:45.786744+00:00
-- url     : https://prove2.me/submissions/a6c4a457-be79-41a0-a27b-282caac8cac5

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
import Theorems.Thm_Psi_cUDraw_prefix
import Theorems.Thm_Psi_isDyckAux_iff
import Theorems.Thm_Psi_runHeight_append
import Theorems.Thm_Psi_runHeight_flatten_UD
import Theorems.Thm_Psi_validFrom_append


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (π : List Bool) (hd : IsDyck π) : IsDyck (π.drop (2 * cUDraw π)) := by
  have hpre := cUDraw_prefix π
  rw [IsDyck, isDyckAux_iff] at hd ⊢
  obtain ⟨hv, he⟩ := hd
  conv at hv => rw [hpre]
  conv at he => rw [hpre]
  rw [validFrom_append, runHeight_flatten_UD] at hv
  rw [runHeight_append, runHeight_flatten_UD] at he
  exact ⟨hv.2, he⟩
end Psi
