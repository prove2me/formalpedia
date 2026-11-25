-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_ord_prod_e2b9c1e6a97e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:24:48.691948+00:00
-- url     : https://prove2.me/submissions/4faf4276-c28f-4636-a860-2fb436fe526b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormLength

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open Module
noncomputable section
variable {R B : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing B]
  [Algebra R B] [Module.Free R B] [Module.Finite R B]
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution {ι : Type*} (s : Finset ι) (a : ι → R) (ha : ∀ i ∈ s, a i ≠ 0) :
    Ring.ord R (∏ i ∈ s, a i) = ∑ i ∈ s, Ring.ord R (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, Ring.ord_mul, ih fun i hi => ha i (by simp [hi])]
    exact mem_nonZeroDivisors_of_ne_zero
      (Finset.prod_ne_zero_iff.mpr fun i hi => ha i (by simp [hi]))
end GroundTheory.Heights₂.Heights.Vertical
