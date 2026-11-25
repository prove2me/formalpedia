-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.hermForm_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:40:15.703197+00:00
-- url     : https://prove2.me/submissions/ed57952a-8723-4af7-a9cc-b20e998a3db4

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegW
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegZ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (t : K) (x y : Fin r → K) : S.h (t • x) y = S.c t * S.h x y := by
  rw [HermForm.h, HermForm.h, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring
end ReciprocityTheory.MultiplicativeHeights.SemiPt
