-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.tor_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:28:02.052742+00:00
-- url     : https://prove2.me/submissions/bc12c864-795a-4703-b6ba-05a1fba6e6e6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_UnitaryTransvectionZeroSecondMemClosure
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_tor_mulVec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}
variable (σ J)
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution (e f : ι → K) (l m : K) : tor σ J e f l m = tor σ J f e m l := by
  have matrix_eq_of_mulVec_eq_lemma_2 {ι : Type _} [Fintype ι] [DecidableEq ι] {K : Type _} [CommRing K] {A B : Matrix ι ι K} (h : ∀ x, A *ᵥ x = B *ᵥ x) : A = B := by
    first
      | exact Matrix.ext_of_mulVec_single fun i => h _
      | exact Matrix.toLin'.injective (LinearMap.ext fun x => by simpa using h x)
  refine matrix_eq_of_mulVec_eq_lemma_2 fun x => ?_
  rw [tor_mulVec, tor_mulVec]
  abel
end ReciprocityTheory.ChartRestriction.G.SA
