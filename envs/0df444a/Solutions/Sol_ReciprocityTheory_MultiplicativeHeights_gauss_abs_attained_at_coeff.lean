-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.gauss_abs_attained_at_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:08.068868+00:00
-- url     : https://prove2.me/submissions/4bd6ec02-b035-464b-aade-8cb9db8c739f

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
theorem _root_.solution (w : FinitePlace K) (f : MvPolynomial σ K) (hf : f ≠ 0) :
    ∃ s ∈ f.support, gaussAbs w f = w (f.coeff s) := by
  obtain ⟨s, hs, hsup⟩ := Finset.exists_mem_eq_sup f.support
    (MvPolynomial.support_nonempty.2 hf) (fun s => (w (f.coeff s)).toNNReal)
  refine ⟨s, hs, ?_⟩
  unfold gaussAbs
  rw [hsup, Real.coe_toNNReal _ (apply_nonneg w _)]
end ReciprocityTheory.MultiplicativeHeights
