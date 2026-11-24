-- Prove2me | solution 1 for Psi.w_length_descent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:35:26.063806+00:00
-- url     : https://prove2.me/submissions/1dd9f853-fa41-418f-bd9a-9fe7b3fbe31b

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
import Theorems.Thm_Psi_noDescent_false_decomp


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution {w : List Bool} (hnd : noDescent w = false) :
    w.length = cLead0 w + cLead1 (w.drop (cLead0 w)) + 1 +
      ((w.drop (cLead0 w)).drop (cLead1 (w.drop (cLead0 w)) + 1)).length := by
  conv_lhs => rw [(noDescent_false_decomp hnd).1]
  simp only [List.length_append, List.length_replicate, List.length_cons]
  omega
end Psi
