-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.coordLat_selfDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:04:33.676348+00:00
-- url     : https://prove2.me/submissions/49598e11-01b6-470f-83f7-03d7fae451ad

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCE
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_coordForm_h
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_mem_coordLat
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_exists_coord
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_coordLat_integral

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
    {b : Fin k → Fin r → K} {S : HermForm K r} (hb : IsKBasisIn B b)
    (hsd : IsSelfDual S B) : IsSelfDual (coordForm S b) (coordLat B b) := by
  refine ⟨coordLat_integral hsd.1, fun s hs => mem_coordLat.2 (hsd.2 _ fun y hy => ?_)⟩
  obtain ⟨t, ht, rfl⟩ := exists_coord hb hy
  rw [coordForm_h]
  exact hs t ht
end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
