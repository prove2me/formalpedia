-- Prove2me | solution 1 for QEC.Locality.measuredTwoThirdsChildren_mem_bkAdmissibleChildPairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:28:15.086433+00:00
-- url     : https://prove2.me/submissions/78b7c5c8-57b0-469a-9a47-4165f11dc4a6

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
import Theorems.Thm_QEC_Locality_measuredTwoThirdsChildren_card_add_le

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    (G : ConnectivityGraph ι) (vertices : Finset ι) (hvertices : vertices.Nonempty) :
    ((measuredTwoThirdsLeft G vertices).card,
      (measuredTwoThirdsRight G vertices).card) ∈
        bkAdmissibleChildPairs vertices.card := by
  apply (mem_bkAdmissibleChildPairs_iff).2
  have hsplit := measuredTwoThirdsSplit_spec G vertices
  exact ⟨measuredTwoThirdsLeft_card_lt G vertices hvertices,
    measuredTwoThirdsRight_card_lt G vertices hvertices,
    measuredTwoThirdsChildren_card_add_le G vertices,
    hsplit.2.2.2.1,
    hsplit.2.2.2.2.1⟩
end QEC.Locality
