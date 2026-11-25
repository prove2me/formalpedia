-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.ptSolveMap_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:28:25.87795+00:00
-- url     : https://prove2.me/submissions/535793b7-4354-4ff6-828d-f21bc38de781

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtOrderProdSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtCoeffSingleSubst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtSolveMapFixedIff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptIntSer_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptIntSer_subst


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
theorem _root_.solution (hN : ∀ i j, N i j ∈ ptIntSub v) (hf : PTGood v f)
    (hA0 : ∀ x, PTGood v x → ∀ s, constantCoeff (A x s) = 0)
    (hAi : ∀ x, PTGood v x → ∀ s, A x s ∈ ptIntSer v τ)
    (hKi : ∀ b, K b ∈ ptIntSer v σ) (hK0 : ∀ b, constantCoeff (K b) = 0)
    (x : Fin d → MvPowerSeries τ C) (hx : PTGood v x) :
    PTGood v (ptSolveMap A K N f x) := by
  intro c
  have hs := hasSubst_of_constantCoeff_zero (hA0 x hx)
  refine ⟨?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply]
    simp only [ptSolveMap, map_sum, coeff_smul, map_sub, coeff_zero_eq_constantCoeff_apply,
      (hf _).1, constantCoeff_subst_eq_zero hs (hA0 x hx) (hK0 _), sub_zero, mul_zero,
      Finset.sum_const_zero]
  · exact Subring.sum_mem _ fun b _ => ptIntSer_smul (hN b c)
      (Subring.sub_mem _ (hf b).2 (ptIntSer_subst hs (hAi x hx) (hKi b)))
end ReciprocityTheory.ChartRestriction.G.Sh
