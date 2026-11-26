-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.manuscript_elementaryAbelian_bottom_index_minFac
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:05:07.895609+00:00
-- url     : https://prove2.me/submissions/eee8deaa-4255-47c9-b88a-7db7dafcd52c

import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
import Definitions.Def_SharpIntermediateSubgroupBounds_GroupMain
import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Definitions.Def_SharpIntermediateSubgroupBounds_Manuscript
import Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_elementaryAbelian_bottom_index

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open Filter
noncomputable section
attribute [local instance] SharpIntermediateSubgroupBounds.manuscriptSubgroupIntervalFintype
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution (p a : ℕ)
    [Fact p.Prime] (ha : 0 < a) :
    (⊥ : Subgroup (ElementaryAbelianGroup p (2 * a))).index.minFac = p := by
  rw [manuscript_elementaryAbelian_bottom_index p a]
  exact (Fact.out : p.Prime).pow_minFac (by omega)
end SharpIntermediateSubgroupBounds
