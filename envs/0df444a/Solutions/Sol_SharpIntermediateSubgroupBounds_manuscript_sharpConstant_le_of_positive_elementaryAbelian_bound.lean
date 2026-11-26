-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.manuscript_sharpConstant_le_of_positive_elementaryAbelian_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:00:23.600525+00:00
-- url     : https://prove2.me/submissions/26cb9f43-ebd1-4622-8ec4-2d1ac48e9e43

import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
import Definitions.Def_SharpIntermediateSubgroupBounds_GroupMain
import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Definitions.Def_SharpIntermediateSubgroupBounds_Manuscript
import Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_elementaryAbelian_even_rank_tendsto_sharpConstant

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open Filter
noncomputable section
attribute [local instance] SharpIntermediateSubgroupBounds.manuscriptSubgroupIntervalFintype
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution
    {p : ℕ} [Fact p.Prime] {C : ℝ}
    (hC : ∀ a : ℕ, 0 < a →
      (p : ℝ)⁻¹ ^ (a * a) *
        (Fintype.card (elementaryAbelianInterval p (2 * a)) : ℝ) ≤ C) :
    sharpConstant (p : ℝ) ≤ C := by
  apply le_of_tendsto
    (manuscript_elementaryAbelian_even_rank_tendsto_sharpConstant (p := p))
  exact Filter.eventually_atTop.2 ⟨1, fun a ha ↦ hC a (by omega)⟩
end SharpIntermediateSubgroupBounds
