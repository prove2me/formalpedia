-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.wa_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:52.010547+00:00
-- url     : https://prove2.me/submissions/f5b19340-5b77-4ac3-823b-5a6d18f3642e

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegAA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_waR_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Module
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r n : ℕ} (S : HermForm K r)
    (x : Fin r → K) (t : Fin n → K) (b : Fin n → Fin r → K) :
    S.h x (∑ i, t i • b i) = ∑ i, t i * S.h x (b i) := by
  rw [← waR_apply S x, map_sum]
  simp only [map_smul, smul_eq_mul, waR_apply]
end ReciprocityTheory.MultiplicativeHeights
