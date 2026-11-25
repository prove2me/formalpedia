-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.sigF_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:58:48.112952+00:00
-- url     : https://prove2.me/submissions/d64a0d43-5e05-4fd1-8150-b630a6a78b88

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DecompBlock0
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ProdZpowEqZpowSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SupportFreeOfBlockSubstInvariant
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
variable {K : Type} [Field K] [CharZero K] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (b : Fin (D + 1)) (u : Kˣ) (g : KTp K D N) :
    sigF (K := K) (D := D) (N := N) b u (algebraMap (KTp K D N) (KTf K D N) g) =
      algebraMap (KTp K D N) (KTf K D N) (sigP b u g) := by
  first
  | exact IsFractionRing.ringEquivOfRingEquiv_algebraMap _ _
  | simp [sigF, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
end ReciprocityTheory.ChartRestriction.G.T0
