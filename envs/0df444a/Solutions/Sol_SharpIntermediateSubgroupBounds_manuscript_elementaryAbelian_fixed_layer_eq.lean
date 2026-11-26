-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.manuscript_elementaryAbelian_fixed_layer_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:05:13.545427+00:00
-- url     : https://prove2.me/submissions/e246ddd1-c2b2-48e0-86e6-5b56b50f5ccc

import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
import Definitions.Def_SharpIntermediateSubgroupBounds_GroupMain
import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Definitions.Def_SharpIntermediateSubgroupBounds_Manuscript
import Theorems.Thm_SharpIntermediateSubgroupBounds_elementaryAbelian_primePowerLayer_card_eq_qBinom


set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open Filter
noncomputable section
attribute [local instance] SharpIntermediateSubgroupBounds.manuscriptSubgroupIntervalFintype
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution (p n k : ℕ)
    [Fact p.Prime] (hk : k ≤ n) :
    (primePowerLayer p k
      (⊥ : Subgroup (ElementaryAbelianGroup p n)) ⊤).card = qBinom p n k :=
  elementaryAbelian_primePowerLayer_card_eq_qBinom p n k hk
end SharpIntermediateSubgroupBounds
