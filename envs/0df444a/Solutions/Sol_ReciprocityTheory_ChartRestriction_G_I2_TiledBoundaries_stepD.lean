-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.stepD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:07:26.780847+00:00
-- url     : https://prove2.me/submissions/7d5093cf-0af2-4c24-982e-e6f4a4da3a8a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_MemSpanBn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_ETSymmApply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_secMap_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory Complex Module
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
theorem _root_.solution : StepD := by
  intro E _ _ X q n hq
  obtain ⟨hfd, hr⟩ := dim (Fin n × Idx X.dim) (YT X n q) q hq
  have hinj := secMap_inj X q n
  refine ⟨Module.Finite.of_injective (secMap X q n) hinj, ?_⟩
  calc Module.finrank ℂ (X.Sec q n) ≤ Module.finrank ℂ ((YT X n q).Sec q) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ ≤ q ^ Fintype.card (Fin n × Idx X.dim) := hr
    _ = q ^ (Fintype.card (Idx X.dim) * n) := by
        rw [Fintype.card_prod, Fintype.card_fin, mul_comm]
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
