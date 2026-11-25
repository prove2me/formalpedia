-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_comap_eq_of_vertical_211dcfa04a62
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:59:05.316273+00:00
-- url     : https://prove2.me/submissions/4ff73ff3-414e-4bd7-baf7-802bb0df82e5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotLtLtOfMemMinimalPrimes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {W U : Ideal (MRing ι)} [W.IsPrime] [U.IsPrime] (hv : ¬ IsHorizontal W)
    (hWU : W ≤ U) : U.comap (C : ℤ →+* MRing ι) = W.comap (C : ℤ →+* MRing ι) := by
  have hmax : (W.comap (C : ℤ →+* MRing ι)).IsMaximal :=
    Ideal.IsPrime.isMaximal (Ideal.comap_isPrime _ _) hv
  exact (hmax.eq_of_le (Ideal.comap_isPrime (C : ℤ →+* MRing ι) U).ne_top (Ideal.comap_mono hWU)).symm
end GroundTheory.Heights₂.Heights.Inter
