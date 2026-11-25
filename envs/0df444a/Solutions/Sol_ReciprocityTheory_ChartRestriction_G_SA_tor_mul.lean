-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.tor_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:40:59.91191+00:00
-- url     : https://prove2.me/submissions/5e6fdc91-03e7-4197-a433-49a25878a68f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_UnitaryTransvectionZeroSecondMemClosure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ConjMemEichSet
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hm_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_tor_hm


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
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ)
include hσ hJ
variable {e f : ι → K} (he : hf σ J e e = 0) (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
include he hff hef
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution (l m l' m' : K) :
    tor σ J e f l m * tor σ J e f l' m' = tor σ J e f (l * l') (m * m') := by
  rw [tor_hm, tor_hm, tor_hm, hm_mul hσ hJ he hff hef]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
end ReciprocityTheory.ChartRestriction.G.SA
