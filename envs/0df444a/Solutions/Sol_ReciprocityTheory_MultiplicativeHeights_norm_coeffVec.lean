-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.norm_coeffVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:27:34.77779+00:00
-- url     : https://prove2.me/submissions/7daf50aa-acc5-4362-938f-c93c981a8d10

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExpTorusMeanLeL2OfLex
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_coeffVec_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Finset
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {ι : Type*} (T : Finset (ι →₀ ℕ)) (P : MvPolynomial ι ℂ)
    (hP : P.support ⊆ T) : ‖coeffVec T P‖ = polyL2 P := by
  classical
  rw [EuclideanSpace.norm_eq, polyL2]
  congr 1
  simp only [coeffVec_apply]
  rw [Finset.sum_coe_sort T (fun t => ‖P.coeff t‖ ^ 2)]
  exact (Finset.sum_subset hP (fun t _ ht => by
    rw [MvPolynomial.notMem_support_iff.mp ht, norm_zero]; ring)).symm
end ReciprocityTheory.MultiplicativeHeights
