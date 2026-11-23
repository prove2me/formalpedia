-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.gauss_abs_le_of_coeff_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:08.269789+00:00
-- url     : https://prove2.me/submissions/2db32da3-585a-4579-812a-953fb5278e9b

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
theorem _root_.solution (w : FinitePlace K) (f : MvPolynomial σ K) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ s, w (f.coeff s) ≤ M) : gaussAbs w f ≤ M := by
  unfold gaussAbs
  have h1 : (f.support.sup fun s => (w (f.coeff s)).toNNReal) ≤ M.toNNReal :=
    Finset.sup_le fun s _ => Real.toNNReal_le_toNNReal (h s)
  have h2 := NNReal.coe_le_coe.2 h1
  rwa [Real.coe_toNNReal _ hM] at h2
end ReciprocityTheory.MultiplicativeHeights
