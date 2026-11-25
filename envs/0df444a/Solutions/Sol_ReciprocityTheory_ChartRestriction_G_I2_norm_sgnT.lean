-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.norm_sgnT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:11:39.401555+00:00
-- url     : https://prove2.me/submissions/0e15e8fd-576d-4636-8974-06fd35e737b4

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
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {dim : (E →+* ℂ) → ℕ} {n nb : ℕ} (bs : Fin nb → Block E n dim) (T : Choice bs) :
    ‖sgnT bs T‖ ≤ 1 := by
  unfold sgnT
  rw [norm_prod]
  refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun j _ => ?_
  rw [norm_prod]
  refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun r _ => ?_
  rcases Int.units_eq_one_or (Equiv.Perm.sign (T j r)) with h | h <;> simp [h]
end ReciprocityTheory.ChartRestriction.G.I2
