-- Prove2me | solution 1 for ThreeSum.BlockEncoding.rightSubset_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:25:57.340743+00:00
-- url     : https://prove2.me/submissions/18126da3-9538-4dce-8f4d-ee840c01040c

import Definitions.Def_Submission_ThreeSum_BlockRows
import Definitions.Def_Submission_ThreeSum_RawPrefixCounts
import Definitions.Def_Submission_ThreeSum_BlockEncoding
import Theorems.Thm_ThreeSum_BlockRows_flat_card_of_balance
import Theorems.Thm_ThreeSum_LocalGraph_edge_data


set_option autoImplicit false
open ThreeSum ThreeSum.BlockEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences BlockRows
namespace ThreeSum.BlockEncoding
theorem _root_.solution {h J : ℕ} (t : ChoiceTuple h J) :
    (rightSubset t).card = J * h :=
  flat_card_of_balance _ (fun i => (edge_data (edge (t i))).2.1)
end ThreeSum.BlockEncoding
