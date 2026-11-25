-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.FPw.S_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:34:47.926865+00:00
-- url     : https://prove2.me/submissions/69f45b57-89c8-4517-a64e-04c45d82ec18

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaIPZeroRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_IteratedFDerivTailZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_ExpNEllMem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_Pf_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_expN_ell_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_paPoly_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex Filter Topology
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2.FPw
theorem _root_.solution {q c : ℕ} (a : EuclideanSpace ℂ ι) {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) (N : ℕ) :
    (fun v => expN N (ellL q a v) * Pf q a F v) ∈ paPoly (N + c) :=
  paPoly_mul (expN_ell_mem q a N) (Pf_mem a hF)
end ReciprocityTheory.ChartRestriction.G.I2.FPw
