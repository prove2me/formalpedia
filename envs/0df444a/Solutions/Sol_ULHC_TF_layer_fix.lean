-- Prove2me | solution 1 for ULHC.TF.layer_fix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:53:24.864284+00:00
-- url     : https://prove2.me/submissions/30bb9cf1-4e9b-4737-aad7-71ea13ec96f1

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
import Theorems.Thm_ULHC_TF_layer_stable
import Theorems.Thm_ULHC_TF_layer_exists_fix

set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF
namespace ULHC.TF
theorem _root_.solution (V : Finset Pt) (F : Finset Edge) (m : ℕ) :
    layer V F (V.card + m) = layer V F V.card := by
  obtain ⟨k, hk, h⟩ := layer_exists_fix V F
  rw [layer_stable h _ (by omega), layer_stable h _ hk]
end ULHC.TF
