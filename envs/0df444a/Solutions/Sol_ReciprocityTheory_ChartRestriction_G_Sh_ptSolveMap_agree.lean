-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.ptSolveMap_agree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:54:35.606244+00:00
-- url     : https://prove2.me/submissions/ff9e9781-33e5-40fe-9d09-1489b706add8

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtOrderProdSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtCoeffSingleSubst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtSolveMapFixedIff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_pt_subst_agree


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
open Classical
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}
variable {d : ℕ} {σ τ : Type*} [Finite σ]
  (A : (Fin d → MvPowerSeries τ C) → σ → MvPowerSeries τ C)
  (K : Fin d → MvPowerSeries σ C) (M N : Matrix (Fin d) (Fin d) C)
  (f : Fin d → MvPowerSeries τ C)
variable {A K}
namespace ReciprocityTheory.ChartRestriction.G.Sh
theorem _root_.solution
    (hA0 : ∀ x, PTGood v x → ∀ s, constantCoeff (A x s) = 0)
    (hAag : ∀ k x y, PTGood v x → PTGood v y → PTAgree k x y →
      ∀ s (e : τ →₀ ℕ), e.degree < k → coeff e (A x s) = coeff e (A y s))
    (hK : ∀ b α, coeff α (K b) ≠ 0 → 2 ≤ α.degree ∨
      ∀ x y, PTGood v x → PTGood v y → ∀ s ∈ α.support, A x s = A y s)
    (k : ℕ) (x y : Fin d → MvPowerSeries τ C) (hx : PTGood v x) (hy : PTGood v y)
    (hxy : PTAgree k x y) :
    PTAgree (k + 1) (ptSolveMap A K N f x) (ptSolveMap A K N f y) := by
  intro c e he
  simp only [ptSolveMap, map_sum, coeff_smul, map_sub]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [pt_subst_agree (hasSubst_of_constantCoeff_zero (hA0 x hx))
    (hasSubst_of_constantCoeff_zero (hA0 y hy)) (hA0 x hx) (hA0 y hy) (K b) k
    (hAag k x y hx hy hxy) (fun α hα => (hK b α hα).imp id (fun h => h x y hx hy)) e he]
end ReciprocityTheory.ChartRestriction.G.Sh
