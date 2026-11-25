-- Prove2me | solution 1 for PI.RayBoundIQW.HData.minC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:12:56.936454+00:00
-- url     : https://prove2.me/submissions/f09c8eb1-106d-4a83-8ec6-b6072870a5b5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ImaginaryQuadraticClassBound_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ImaginaryQuadraticClassBound_ClassNum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.InfinitePlace
open scoped nonZeroDivisors
open PI PI.RayBoundIQW
variable {R : Type*} [CommRing R]
namespace PI.RayBoundIQW
namespace HData
theorem _root_.solution {I : Ideal R} {e1 e2 : R} {a c b : ℕ} (hP : HData I e1 e2 a c b)
    (x y : ℤ) (hx : (x : R) * e1 + (y : R) * e2 ∈ I) (h1 : -(c : ℤ) < y) (h2 : y < c) :
    y = 0 := by
  obtain ⟨-, -, -, -, -, -, hcmin⟩ := hP
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · refine hcmin (-y).toNat (by omega) (by omega) (-x) ?_
    have e : ((((-y).toNat : ℕ) : ℤ) : R) = -(y : R) := by
      rw [Int.toNat_of_nonneg (by omega)]; push_cast; ring
    rw [e]
    convert I.neg_mem hx using 1; push_cast; ring
  · refine hcmin y.toNat (by omega) (by omega) x ?_
    rwa [Int.toNat_of_nonneg hpos.le]
end HData
end PI.RayBoundIQW
