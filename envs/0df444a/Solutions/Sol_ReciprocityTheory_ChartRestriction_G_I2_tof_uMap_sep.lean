-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.tof_uMap_sep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:42:11.350063+00:00
-- url     : https://prove2.me/submissions/39b0ea4e-fe24-4dfa-8344-03c91a0e02f4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofSpanCondition
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofFinrankIRLe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_isU_uMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) {x x' : Vsp X.dim} (hx : x ∈ X.L) (hx' : x' ∈ X.L)
    (hne : uMap I x ≠ uMap I x') : 1 ≤ ‖uMap I x - uMap I x'‖ := by
  have hsub : uMap I x - uMap I x' = uMap I (x - x') := (map_sub (uMap I) x x').symm
  have hne' : uMap I (x - x') ≠ 0 := by
    rw [← hsub]
    exact sub_ne_zero.mpr hne
  have hb := hI.sep (x - x') (X.L.sub_mem hx hx') (uMap I (x - x')) (isU_uMap I (x - x')) hne'
  have h1 : (1 : ℝ) ≤ ‖uMap I (x - x')‖ ^ 2 := le_trans P.C2 hb
  rw [hsub]
  by_contra hlt
  have hlt' : ‖uMap I (x - x')‖ < 1 := lt_of_not_ge hlt
  have h0 := norm_nonneg (uMap I (x - x'))
  nlinarith
end ReciprocityTheory.ChartRestriction.G.I2
