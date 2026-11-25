-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.eU_props
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:10:49.133946+00:00
-- url     : https://prove2.me/submissions/bee06df2-51a5-49c5-8efc-661654808984

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CardChoiceLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfNormLeTwo

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
variable {E : Type} [Field E] [NumberField E]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {dim : (E →+* ℂ) → ℕ} {n nb : ℕ} (bs : Fin nb → Block E n dim) (j : Fin nb)
    (a : Fin (bs j).i) : InPart (bs j).τ (eU bs j a) ∧ ‖eU bs j a‖ = 1 := by
  refine ⟨fun k hk => ?_, by simp [eU]⟩
  simp only [eU, PiLp.single_apply]
  rw [if_neg]
  rintro rfl
  exact hk rfl
end ReciprocityTheory.ChartRestriction.G.I2
