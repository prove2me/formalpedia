-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.wa_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:06:07.680619+00:00
-- url     : https://prove2.me/submissions/8c551f61-54d0-4311-afa6-5c9349e93f12

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegAA

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
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (a : K) (x y : Fin r → K) : S.h (a • x) y = S.c a * S.h x y := by
  simp only [HermForm.h, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
end ReciprocityTheory.MultiplicativeHeights
