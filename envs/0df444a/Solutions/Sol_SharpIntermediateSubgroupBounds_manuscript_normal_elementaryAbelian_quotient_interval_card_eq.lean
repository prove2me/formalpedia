-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.manuscript_normal_elementaryAbelian_quotient_interval_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:05:20.220197+00:00
-- url     : https://prove2.me/submissions/c8cf459d-d617-4554-b0ea-41b53a656a13

import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
import Definitions.Def_SharpIntermediateSubgroupBounds_GroupMain
import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Definitions.Def_SharpIntermediateSubgroupBounds_Manuscript
import Theorems.Thm_SharpIntermediateSubgroupBounds_normal_elementaryAbelian_quotient_interval_card_eq


set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open Filter
noncomputable section
attribute [local instance] SharpIntermediateSubgroupBounds.manuscriptSubgroupIntervalFintype
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution
    {G : Type*} [Group G] [Fintype G] {p n : ℕ}
    (H : Subgroup G) [H.Normal]
    (e : (G ⧸ H) ≃* ElementaryAbelianGroup p n) [Fact p.Prime] :
    Fintype.card (Set.Ici H) = totalQBinom p n :=
  normal_elementaryAbelian_quotient_interval_card_eq H e
end SharpIntermediateSubgroupBounds
