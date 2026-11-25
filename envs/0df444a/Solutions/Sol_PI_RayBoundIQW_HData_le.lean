-- Prove2me | solution 1 for PI.RayBoundIQW.HData.le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:18:32.162145+00:00
-- url     : https://prove2.me/submissions/643ed0f2-1c6f-4dad-a37a-d78a9e348055

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ImaginaryQuadraticClassBound_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ImaginaryQuadraticClassBound_ClassNum
import Theorems.Thm_PI_RayBoundIQW_HData_minA
import Theorems.Thm_PI_RayBoundIQW_HData_minC

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
theorem _root_.solution {I J : Ideal R} {e1 e2 : R} {a c b : ℕ}
    (hspan : ∀ z : R, ∃ x y : ℤ, z = (x : R) * e1 + (y : R) * e2)
    (hP : HData I e1 e2 a c b) (haJ : ((a : ℤ) : R) * e1 ∈ J)
    (hbJ : ((b : ℤ) : R) * e1 + ((c : ℤ) : R) * e2 ∈ J) : I ≤ J := by
  intro z hz
  obtain ⟨x, y, rfl⟩ := hspan z
  have hc0 : (0 : ℤ) < c := by exact_mod_cast hP.2.1
  have ha0 : (0 : ℤ) < a := by exact_mod_cast hP.1
  obtain ⟨q, r, hr0, hrc, rfl⟩ : ∃ q r : ℤ, 0 ≤ r ∧ r < c ∧ y = c * q + r :=
    ⟨y / c, y % c, Int.emod_nonneg _ hc0.ne', Int.emod_lt_of_pos _ hc0,
      (Int.mul_ediv_add_emod y c).symm⟩
  have hz1 : ((x - q * b : ℤ) : R) * e1 + (r : R) * e2 ∈ I := by
    have := I.sub_mem hz (I.mul_mem_left (q : R) hP.2.2.2.2.1)
    convert this using 1; push_cast; ring
  have hr : r = 0 := hP.minC _ _ hz1 (by omega) hrc
  subst hr
  obtain ⟨q', t, ht0, hta, hs⟩ : ∃ q' t : ℤ, 0 ≤ t ∧ t < a ∧ x - q * b = a * q' + t :=
    ⟨(x - q * b) / a, (x - q * b) % a, Int.emod_nonneg _ ha0.ne', Int.emod_lt_of_pos _ ha0,
      (Int.mul_ediv_add_emod _ _).symm⟩
  have hz2 : (t : R) * e1 ∈ I := by
    have := I.sub_mem hz1 (I.mul_mem_left (q' : R) hP.2.2.2.1)
    convert this using 1; rw [hs]; push_cast; ring
  have ht : t = 0 := hP.minA _ hz2 (by omega) hta
  subst ht
  have hx : x = a * q' + q * b := by linarith
  subst hx
  have := J.add_mem (J.mul_mem_left (q' : R) haJ) (J.mul_mem_left (q : R) hbJ)
  convert this using 1; push_cast; ring
end HData
end PI.RayBoundIQW
