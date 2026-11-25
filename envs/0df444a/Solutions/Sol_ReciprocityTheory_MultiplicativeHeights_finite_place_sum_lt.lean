-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.finite_place_sum_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:09:01.024542+00:00
-- url     : https://prove2.me/submissions/fe541909-727e-4ae5-8fbe-71da07f0e575

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
theorem _root_.solution {ι : Type*} (w : FinitePlace K) (t : Finset ι) (a : ι → K) {M : ℝ}
    (hM : 0 < M) (h : ∀ i ∈ t, w (a i) < M) : w (∑ i ∈ t, a i) < M := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hM
  | insert j t hj ih =>
    rw [Finset.sum_insert hj]
    refine (FinitePlace.add_le w _ _).trans_lt (max_lt (h j (Finset.mem_insert_self j t)) ?_)
    exact ih fun i hi => h i (Finset.mem_insert_of_mem hi)
end ReciprocityTheory.MultiplicativeHeights
