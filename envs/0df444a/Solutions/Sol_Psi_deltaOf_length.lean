-- Prove2me | solution 1 for Psi.deltaOf_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:35:30.701604+00:00
-- url     : https://prove2.me/submissions/c8ba037c-be6e-425e-b23b-707cabd6dc5e

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
import Theorems.Thm_Psi_deltaAux_length

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (γ : List ℕ) : (deltaOf γ).length = γ.length := deltaAux_length γ 0
end Psi
