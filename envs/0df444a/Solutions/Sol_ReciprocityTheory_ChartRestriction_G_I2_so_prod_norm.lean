-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.so_prod_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:14:58.997817+00:00
-- url     : https://prove2.me/submissions/f4414264-debe-4a03-bdbe-51b60f995cb5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitOA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (x : E) : ∏ σ : E →+* ℂ, ‖σ x‖ = |(Algebra.norm ℚ x : ℝ)| := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun σ => ‖σ x‖) (fun τ => ‖τ x‖) (fun σ => rfl),
    ← norm_prod, ← h, eq_ratCast, Complex.norm_ratCast]
end ReciprocityTheory.ChartRestriction.G.I2
