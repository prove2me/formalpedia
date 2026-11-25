-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.PT.l2_one_eq_toGT_l2_col1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:39:55.844077+00:00
-- url     : https://prove2.me/submissions/c8be10d8-7c2f-4a10-a3f6-cdfa27d46f30

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_DimStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContDiffOfDifferentiableFd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SupRatioLeOfPhaseZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_PT_pointNormSq_column
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex NumberField
noncomputable section
variable {E : Type} [Field E] [NumberField E]
open ReciprocityTheory.ChartRestriction.G.I2.PT
variable (X : PT E)
namespace ReciprocityTheory.ChartRestriction.G.I2.PT
theorem _root_.solution (s : (Fin 1 → Vsp X.dim) → ℂ) : X.l2 1 s = X.toGT.l2 1 (X.col1 s) := by
  have hfd : X.fd 1 = (MeasurableEquiv.funUnique (Fin 1) (Vsp X.dim)) ⁻¹'
      ZSpan.fundamentalDomain X.b := by
    ext v
    simp only [PT.fd, Set.mem_setOf_eq, Set.mem_preimage]
    exact ⟨fun h => h default, fun h k => by rwa [Subsingleton.elim k default]⟩
  have hf : ∀ v : Fin 1 → Vsp X.dim, X.ptN2 1 s v =
      X.toGT.ptN2 1 (X.col1 s) (MeasurableEquiv.funUnique (Fin 1) (Vsp X.dim) v) := by
    intro v
    have hv : v = fun _ => v default := funext fun k => by rw [Subsingleton.elim k default]
    rw [hv, pointNormSq_column]
    rfl
  have hmp := MeasureTheory.volume_preserving_funUnique (Fin 1) (Vsp X.dim)
  have he := (MeasurableEquiv.funUnique (Fin 1) (Vsp X.dim)).measurableEmbedding
  unfold PT.l2 GT.l2
  rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq, hfd]
  simp only [MeasureTheory.measureReal_def]
  erw [hmp.measure_preimage_emb he]
  simp_rw [hf]
  erw [hmp.setIntegral_preimage_emb he (X.toGT.ptN2 1 (X.col1 s))]
  rfl
end ReciprocityTheory.ChartRestriction.G.I2.PT
