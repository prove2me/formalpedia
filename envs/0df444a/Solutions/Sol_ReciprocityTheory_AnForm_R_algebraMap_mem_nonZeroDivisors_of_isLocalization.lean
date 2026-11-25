-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.algebraMap_mem_nonZeroDivisors_of_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:33:50.326262+00:00
-- url     : https://prove2.me/submissions/42055502-7d03-4e91-91f2-5723b8737daa

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory
noncomputable section
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S] {a : R} (ha : a ∈ nonZeroDivisors R) :
    algebraMap R S a ∈ nonZeroDivisors S := by
  rw [mem_nonZeroDivisors_iff_right] at ha ⊢
  intro x hx
  obtain ⟨⟨y, m⟩, rfl⟩ := IsLocalization.mk'_surjective M x
  have h1 : algebraMap R S (y * a) = 0 := by
    rw [map_mul, ← IsLocalization.mk'_spec S y m, mul_right_comm, hx, zero_mul]
  obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff M S _).1 h1
  exact (IsLocalization.mk'_eq_zero_iff y m).2 ⟨c, ha _ (by rw [← hc, mul_assoc])⟩
end ReciprocityTheory.AnForm.R
