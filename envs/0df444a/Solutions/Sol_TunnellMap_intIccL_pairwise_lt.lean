-- Prove2me | solution 1 for TunnellMap.intIccL_pairwise_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:31:51.522246+00:00
-- url     : https://prove2.me/submissions/1719f707-1341-434d-82dc-070fef69ed5e

import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_KernelGenerator

set_option autoImplicit true
open TunnellMap
open OrderedGenerator
namespace TunnellMap
theorem _root_.solution (lo hi : ℤ) : (intIccL lo hi).Pairwise (· < ·) := by
  unfold intIccL
  by_cases h : lo ≤ hi
  · rw [if_pos h]
    rw [List.pairwise_map]
    exact List.Pairwise.imp (fun {a b} (hab : a < b) => by omega)
      (List.pairwise_lt_range (n := (hi - lo).toNat + 1))
  · rw [if_neg h]; exact List.Pairwise.nil
end TunnellMap
