-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.coordLat_fg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:11.041479+00:00
-- url     : https://prove2.me/submissions/2cecc516-c531-44db-a752-3e210c4bd6a3

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCE
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_combMap_injective
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_map_coordLat

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
    {b : Fin k → Fin r → K} (hB : B.FG) (hb : IsKBasisIn B b) : (coordLat B b).FG := Submodule.fg_of_fg_map_injective ((combMap b).restrictScalars (𝓞 K)) (combMap_injective hb.2.1) (by rw [map_coordLat hb]; exact hB)
end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
