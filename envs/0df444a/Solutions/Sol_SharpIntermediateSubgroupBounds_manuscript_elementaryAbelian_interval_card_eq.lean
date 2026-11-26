-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.manuscript_elementaryAbelian_interval_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:58:20.894795+00:00
-- url     : https://prove2.me/submissions/858dcb41-9f0b-4804-b89b-9e1cccb0ae36

import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
import Definitions.Def_SharpIntermediateSubgroupBounds_GroupMain
import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Definitions.Def_SharpIntermediateSubgroupBounds_Manuscript
import Theorems.Thm_SharpIntermediateSubgroupBounds_elementaryAbelian_interval_card_eq_totalQBinom


set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open Filter
noncomputable section
attribute [local instance] SharpIntermediateSubgroupBounds.manuscriptSubgroupIntervalFintype
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution (p n : ℕ)
    [Fact p.Prime] :
    Fintype.card (elementaryAbelianInterval p n) = totalQBinom p n :=
  elementaryAbelian_interval_card_eq_totalQBinom p n
end SharpIntermediateSubgroupBounds
