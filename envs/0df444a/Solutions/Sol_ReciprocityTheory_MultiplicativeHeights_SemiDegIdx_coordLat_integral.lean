-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.coordLat_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:29:50.538303+00:00
-- url     : https://prove2.me/submissions/8288e8bf-6378-4e07-a36e-0df399645ea8

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCE
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_coordForm_h
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_mem_coordLat

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
    {b : Fin k → Fin r → K} {S : HermForm K r} (hint : IsIntegralOn S B) :
    IsIntegralOn (coordForm S b) (coordLat B b) := by
  intro s hs t ht
  rw [← coordForm_h]
  exact hint _ (mem_coordLat.1 hs) _ (mem_coordLat.1 ht)
end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
