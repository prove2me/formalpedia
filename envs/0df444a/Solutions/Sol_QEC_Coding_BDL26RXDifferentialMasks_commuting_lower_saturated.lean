-- Prove2me | solution 1 for QEC.Coding.BDL26RXDifferentialMasks.commuting_lower_saturated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:40:13.432547+00:00
-- url     : https://prove2.me/submissions/46dea963-66d4-4916-ae54-cce5a224bc18

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
import Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_native_mask_commutes_iff

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXDifferentialMasks
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXQConcreteCoherence
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26RXDifferentialMasks
theorem _root_.solution (h : i.val % 2 = 0)
    (A : Finset (state S i.val).presentation.Q)
    (B : Finset (FamilyZ S depth i.succ))
    (hc : ∀ w, maskWord B (nativeDifferential S depth i w) =
      nativeDifferential S depth i (maskWord A w)) : IncidenceSaturated S depth i A := by
  have hh := (native_mask_commutes_iff S depth i h A B).mp hc
  intro q hq r z hqz hrz
  exact (hh r z 0 hrz).mp ((hh q z 0 hqz).mpr hq)
end QEC.Coding.BDL26RXDifferentialMasks
