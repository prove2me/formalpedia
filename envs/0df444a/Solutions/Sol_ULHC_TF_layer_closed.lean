-- Prove2me | solution 1 for ULHC.TF.layer_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:55:04.29927+00:00
-- url     : https://prove2.me/submissions/38d4445b-d0dd-42d9-b030-66b7e3e7fffa

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
import Theorems.Thm_ULHC_TF_mem_layer_succ
import Theorems.Thm_ULHC_TF_layer_fix

set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF
namespace ULHC.TF
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} {u v : Pt}
    (hu : u ∈ layer V F V.card) (hv : v ∈ nbr V F u) : v ∈ layer V F V.card := by
  rw [← layer_fix V F 1]
  exact mem_layer_succ.2 (Or.inr ⟨u, hu, hv⟩)
end ULHC.TF
