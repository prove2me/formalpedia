-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.map_coordLat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:08.552435+00:00
-- url     : https://prove2.me/submissions/4ac4170a-5607-4c0b-a48c-c29155587451

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCE
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_mem_coordLat
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_exists_coord

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
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} (hb : IsKBasisIn B b) :
    (coordLat B b).map ((combMap b).restrictScalars (𝓞 K)) = B := by
  ext y
  refine ⟨fun h => ?_, fun hy => ?_⟩
  · obtain ⟨t, ht, rfl⟩ := Submodule.mem_map.1 h
    exact mem_coordLat.1 ht
  · obtain ⟨t, ht, rfl⟩ := exists_coord hb hy
    exact Submodule.mem_map.2 ⟨t, ht, rfl⟩
end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
