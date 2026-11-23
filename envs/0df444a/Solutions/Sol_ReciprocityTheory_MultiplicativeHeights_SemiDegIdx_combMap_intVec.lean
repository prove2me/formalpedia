-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.combMap_intVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:07.96625+00:00
-- url     : https://prove2.me/submissions/86bcc21c-d89d-459b-a752-b34b1dd83e3c

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCE
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_combMap_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
open NumberField Matrix
open scoped nonZeroDivisors
namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r k : ℕ}
    {b : Fin k → Fin r → K} {t : Fin k → K} (ht : t ∈ intVec K k)
    (P : Submodule (𝓞 K) (Fin r → K)) (hP : ∀ i, b i ∈ P) : combMap b t ∈ P := by
  rw [combMap_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨x, hx⟩ := Submodule.mem_one.1 ((Submodule.mem_pi).1 ht i (Set.mem_univ i))
  rw [← hx, algebraMap_smul]
  exact P.smul_mem x (hP i)
end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
