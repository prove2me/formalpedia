-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.l2_tens_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:26:50.191456+00:00
-- url     : https://prove2.me/submissions/44d435e1-5e35-4997-b549-c7282a29fc57

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormFundamentalDomain
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_pointNormSq_tensor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_avg_fd_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_l2_norm_fundamental_domain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E] (X : PT E)
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {n : ℕ} (q : ℕ) (s : Fin n → (Fin 1 → Vsp X.dim) → ℂ) :
    X.l2 q (tens X s) = ∏ k, X.l2 q (s k) := by
  rw [Finset.prod_congr rfl fun k _ => l2_norm_fundamental_domain X q (s k)]
  rw [PT.l2]
  simp_rw [pointNormSq_tensor X q s]
  exact avg_fd_prod X (fun k x => X.ptN2 q (s k) (fun _ => x))
end ReciprocityTheory.ChartRestriction.G.I2
