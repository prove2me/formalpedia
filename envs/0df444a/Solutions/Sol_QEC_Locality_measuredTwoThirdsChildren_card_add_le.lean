-- Prove2me | solution 1 for QEC.Locality.measuredTwoThirdsChildren_card_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:25:03.407451+00:00
-- url     : https://prove2.me/submissions/c709d435-d9f8-4066-aa64-ef3538fd5976

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
import Theorems.Thm_QEC_Locality_measuredTwoThirdsLeft_subset
import Theorems.Thm_QEC_Locality_measuredTwoThirdsRight_subset


set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    (G : ConnectivityGraph ι) (vertices : Finset ι) :
    (measuredTwoThirdsLeft G vertices).card +
        (measuredTwoThirdsRight G vertices).card ≤ vertices.card := by
  have hsplit := measuredTwoThirdsSplit_spec G vertices
  have hcardUnion :
      (measuredTwoThirdsLeft G vertices ∪ measuredTwoThirdsRight G vertices).card =
        (measuredTwoThirdsLeft G vertices).card +
          (measuredTwoThirdsRight G vertices).card :=
    Finset.card_union_of_disjoint hsplit.2.2.1
  have hsubset :
      measuredTwoThirdsLeft G vertices ∪ measuredTwoThirdsRight G vertices ⊆ vertices := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact measuredTwoThirdsLeft_subset G vertices hx
    · exact measuredTwoThirdsRight_subset G vertices hx
  rw [← hcardUnion]
  exact Finset.card_le_card hsubset
end QEC.Locality
