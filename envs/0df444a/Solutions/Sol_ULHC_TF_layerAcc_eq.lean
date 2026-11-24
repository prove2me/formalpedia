-- Prove2me | solution 1 for ULHC.TF.layerAcc_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:24:06.26535+00:00
-- url     : https://prove2.me/submissions/6fed385e-8818-487b-9477-a1907e0fc538

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor

set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF
namespace ULHC.TF
theorem _root_.solution (V : Finset Pt) (F : Finset Edge) (k : ℕ) :
    layerAcc V F k = layer V F k :: layersBelow V F k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [layerAcc, ih]; rfl
end ULHC.TF
