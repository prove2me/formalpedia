-- Prove2me | solution 1 for QEC.Coding.BDL26RXDifferentialMasks.incidenceHull_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T22:27:35.241546+00:00
-- url     : https://prove2.me/submissions/df9faf2e-ad3e-4097-8ce5-806b8af33dd1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
import Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_subset_incidenceHull
import Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_incidenceHull_saturated
import Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_incidenceHull_minimal

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXDifferentialMasks
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXQConcreteCoherence
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26RXDifferentialMasks
theorem _root_.solution (A : Finset (state S i.val).presentation.Q) :
    incidenceHull S depth i A = A ↔ IncidenceSaturated S depth i A := by
  constructor
  · intro he
    rw [← he]
    exact incidenceHull_saturated S depth i A
  · intro hs
    exact Finset.Subset.antisymm
      (incidenceHull_minimal S depth i A A (fun _ h => h) hs)
      (subset_incidenceHull S depth i A)
end QEC.Coding.BDL26RXDifferentialMasks
