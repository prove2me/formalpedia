-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.polyL2_eq_sqrt_coeff_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T06:10:51.724122+00:00
-- url     : https://prove2.me/submissions/e9633fd2-de16-492e-99a9-f2471ddff89f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HupsTwCoeffCoeff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_MinkSat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SatDegLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HupsChooseRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PolyL2EqSqrtCoeffSum
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
open NumberField
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {σ : Type*} (f : MvPolynomial σ ℂ) (V : Finset (σ →₀ ℕ)) {r : ℕ}
    (e : V ≃ Fin r) (hf : f.support ⊆ V) :
    ReciprocityTheory.MultiplicativeHeights.polyL2 f = Real.sqrt (∑ i, ‖f.coeff (e.symm i : σ →₀ ℕ)‖ ^ 2) := by
  unfold ReciprocityTheory.MultiplicativeHeights.polyL2
  congr 1
  rw [Finset.sum_subset hf fun s _ hs => by simp [MvPolynomial.notMem_support_iff.1 hs],
    ← Finset.sum_coe_sort V]
  exact (Equiv.sum_comp e.symm (fun x : V => ‖f.coeff (x : σ →₀ ℕ)‖ ^ 2)).symm
end ReciprocityTheory.ChartRestriction.G.T0
