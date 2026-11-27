-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.isUnit_det_of_span_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:32:28.812699+00:00
-- url     : https://prove2.me/submissions/7b0ae44c-414c-42df-b388-aa77afc49d7b

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitDetOfSpanEq
import Theorems.Thm_ReciprocityTheory_PGsh_L2_valuation_det_eq_of_span_eq_alt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (hv : v.Integers R) {X : Type} [Fintype X] [DecidableEq X]
    {P Q : Matrix X X C} (hP : IsUnit P.det)
    (h : Submodule.span R (Set.range fun j x => P x j) =
      Submodule.span R (Set.range fun j x => Q x j)) : IsUnit Q.det := by
  have hvQ := valuation_det_eq_of_span_eq_alt hv hP h
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  rw [h0, map_zero] at hvQ
  exact (Valuation.ne_zero_iff v).2 hP.ne_zero hvQ.symm
end ReciprocityTheory.PGsh.L2
