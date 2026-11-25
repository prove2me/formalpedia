-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.gaussAbs_coeffIn_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:56:56.337084+00:00
-- url     : https://prove2.me/submissions/f7d2cca8-00bd-40ea-b78f-75d53b842818

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_LagrangeIdealLiftsFact
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ContinuousTorusPoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NatDegreeLeAndCoeffProdPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LogHeightLeTorusHeightSubst
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_coeff_le_gauss_abs
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_finite_place_sum_le
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_abs_le_of_coeff_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {V : Type*} (w : FinitePlace K) (i : V) (k : ℕ)
    (P : MvPolynomial V K) :
    ReciprocityTheory.MultiplicativeHeights.gaussAbs w (ReciprocityTheory.MultiplicativeHeights.coeffIn i k P) ≤ ReciprocityTheory.MultiplicativeHeights.gaussAbs w P := by
  classical
  have h0 : 0 ≤ ReciprocityTheory.MultiplicativeHeights.gaussAbs w P := by unfold ReciprocityTheory.MultiplicativeHeights.gaussAbs; exact NNReal.coe_nonneg _
  refine ReciprocityTheory.MultiplicativeHeights.gauss_abs_le_of_coeff_le w _ h0 fun t => ?_
  unfold ReciprocityTheory.MultiplicativeHeights.coeffIn
  rw [MvPolynomial.coeff_sum]
  refine ReciprocityTheory.MultiplicativeHeights.finite_place_sum_le w _ _ h0 fun s _ => ?_
  rw [MvPolynomial.coeff_monomial]
  split_ifs
  · exact ReciprocityTheory.MultiplicativeHeights.coeff_le_gauss_abs w P s
  · rw [map_zero]; exact h0
end ReciprocityTheory.ChartRestriction.G.T0
