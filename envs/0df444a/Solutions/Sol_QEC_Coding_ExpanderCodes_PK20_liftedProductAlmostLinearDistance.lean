-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.PK20.liftedProductAlmostLinearDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:57:33.809772+00:00
-- url     : https://prove2.me/submissions/0b68cb25-d600-41dd-971b-9c54e29e5a2b

import Definitions.Def_QEC_Coding_ExpanderCodes_Tradeoff
import Definitions.Def_QEC_Results_QLDPC_LiftedProductAlmostLinear
import Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_firstAlmostLinearFamily_of_propositionOne
import Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_twoProductConstructionFamily_of_propositionOne


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
namespace QEC.Coding.ExpanderCodes.PK20
theorem _root_.solution
    (hPropositionOne : PropositionOneExpandingMatrixFamily) :
    LiftedProductAlmostLinearDistance := by
  exact ⟨firstAlmostLinearFamily_of_propositionOne hPropositionOne,
    twoProductConstructionFamily_of_propositionOne hPropositionOne⟩
end QEC.Coding.ExpanderCodes.PK20
