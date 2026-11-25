-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.card_mPiece_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:56:11.907772+00:00
-- url     : https://prove2.me/submissions/cf8fde26-1d6f-42e1-a3cb-b551caa60aa1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsPrimeFiltrationOfIsMultiHomogIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsHomogeneousGrL
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_range_pieceMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
attribute [local instance 2000] lexDecEq
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (J : Ideal (MRing ι)) (a : K → ℕ) :
    Nat.card (mPiece J a) = Nat.card (mHom ι a ⧸ LinearMap.ker (pieceMap J a)) := by
  rw [← range_pieceMap]
  exact Nat.card_congr (LinearMap.quotKerEquivRange _).toEquiv.symm
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
