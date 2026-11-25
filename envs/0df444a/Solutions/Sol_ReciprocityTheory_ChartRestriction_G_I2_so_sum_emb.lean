-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.so_sum_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:31:43.403831+00:00
-- url     : https://prove2.me/submissions/70e638f3-9da6-4ebc-9c0f-0c7595fe6fd5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitOA
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_TransferenceMinima
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitO
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_soPsi_apply
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply


attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.soPsi_apply

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (x : E) : ∑ σ : E →+* ℂ, σ x = ((Algebra.trace ℚ E x : ℚ) : ℂ) := by
  rw [← eq_ratCast (algebraMap ℚ ℂ), trace_eq_sum_embeddings (E := ℂ)]
  exact Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) _ _
    fun σ => by simp [RingHom.equivRatAlgHom_apply]
end ReciprocityTheory.ChartRestriction.G.I2
