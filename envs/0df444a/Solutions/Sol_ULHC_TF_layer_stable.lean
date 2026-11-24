-- Prove2me | solution 1 for ULHC.TF.layer_stable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:46:30.721517+00:00
-- url     : https://prove2.me/submissions/e766709e-e643-40c6-bed7-6baee0a35469

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
import Theorems.Thm_ULHC_TF_layer_succ
import Theorems.Thm_ULHC_Conn_refl


set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF
namespace ULHC.TF
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} {k : ℕ}
    (h : layer V F (k + 1) = layer V F k) : ∀ j, k ≤ j → layer V F j = layer V F k := by
  intro j hj
  induction hj with
  | refl => rfl
  | step _ ih => rw [layer_succ, ih, ← layer_succ, h]
end ULHC.TF
