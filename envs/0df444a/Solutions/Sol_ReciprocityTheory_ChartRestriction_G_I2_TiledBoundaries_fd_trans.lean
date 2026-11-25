-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.fd_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:03:31.720928+00:00
-- url     : https://prove2.me/submissions/2ea19885-07a0-4d86-9dec-2e17681511b3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_PointwiseNormSqPullbackTensorEqProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_MemSpanBn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_fd_fund
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
theorem _root_.solution (X : PT E) (n : ℕ) (a : Fin n → Vsp X.dim) :
    IsAddFundamentalDomain (Submodule.span ℤ (Set.range (Bn X n))).toAddSubgroup
      ((fun u => u + a) ⁻¹' X.fd n) volume := by
  refine (fd_fund X n).preimage_of_equiv (measurePreserving_add_right volume a).quasiMeasurePreserving
    (e := id) Function.bijective_id (fun g x => ?_)
  show ((g : Fin n → Vsp X.dim) + x) + a = (g : Fin n → Vsp X.dim) + (x + a)
  exact add_assoc _ _ _
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
