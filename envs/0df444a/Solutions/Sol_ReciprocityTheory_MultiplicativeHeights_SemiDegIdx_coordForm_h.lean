-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.coordForm_h
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:16:43.639174+00:00
-- url     : https://prove2.me/submissions/7ef4facc-f5db-4cff-a5dc-95b3bb01c05d

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCE
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_hermForm_sum_right
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_hermForm_smul_right
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_combMap_apply
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_succ
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_zero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_hermForm_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_succ
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_zero



set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
open NumberField Matrix
open scoped nonZeroDivisors
namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r k : ℕ} (S : HermForm K r)
    (b : Fin k → Fin r → K) (s t : Fin k → K) :
    S.h (combMap b s) (combMap b t) = (coordForm S b).h s t := by
  have key : ∀ j, S.h (combMap b s) (b j) = ∑ i, S.c (s i) * S.h (b i) (b j) := by
    intro j
    rw [← hermForm_conj S (b j), combMap_apply, hermForm_sum_right, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hermForm_smul_right, map_mul, hermForm_conj]
  show _ = ∑ i, ∑ j, S.c (s i) * S.h (b i) (b j) * t j
  rw [combMap_apply b t, hermForm_sum_right]
  simp only [hermForm_smul_right, key, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
