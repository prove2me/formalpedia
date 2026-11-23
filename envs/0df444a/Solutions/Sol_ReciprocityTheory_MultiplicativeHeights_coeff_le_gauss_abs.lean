-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.coeff_le_gauss_abs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:58.31454+00:00
-- url     : https://prove2.me/submissions/36c57cb0-9eed-46c4-b058-981cfc5df33e

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_Lemmata_GeneralBFactLeftExtra_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussAbsMulOfMonomialOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open NumberField
variable {K : Type*} [Field K] [NumberField K] {σ : Type*}
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (w : FinitePlace K) (f : MvPolynomial σ K) (s : σ →₀ ℕ) :
    w (f.coeff s) ≤ gaussAbs w f := by
  unfold gaussAbs
  by_cases hs : s ∈ f.support
  · have h := Finset.le_sup (f := fun s => (w (f.coeff s)).toNNReal) hs
    have h2 : ((w (f.coeff s)).toNNReal : ℝ) ≤ _ := NNReal.coe_le_coe.2 h
    rwa [Real.coe_toNNReal _ (apply_nonneg w _)] at h2
  · rw [MvPolynomial.notMem_support_iff.1 hs, map_zero]
    exact NNReal.coe_nonneg _
end ReciprocityTheory.MultiplicativeHeights
