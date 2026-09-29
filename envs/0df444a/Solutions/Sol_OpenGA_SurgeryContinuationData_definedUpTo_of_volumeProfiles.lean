-- Prove2me | solution 1 for OpenGA.SurgeryContinuationData.definedUpTo_of_volumeProfiles
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-10T18:40:04.547893+00:00
-- url     : https://prove2.me/submissions/cbd67971-6b15-4113-83fe-bbbd62d1e113

import Theorems.Thm_OpenGA_SurgeryVolumeProfile_surgeryTimes_finite
import Theorems.Thm_OpenGA_SurgeryContinuationData_definedUpTo_of_locallyFinite

set_option autoImplicit false

open Set

theorem solution (C : OpenGA.SurgeryContinuationData)
    (prof : ∀ T : ℝ, 0 < T → OpenGA.SurgeryVolumeProfile 0 T)
    (hprof : ∀ (T : ℝ) (hT : 0 < T),
      (prof T hT).surgeryTimes = C.surgeryTimes ∩ Ioc 0 T)
    (hpos : ∀ t ∈ C.surgeryTimes, 0 < t) (T : ℝ) (hT : 0 ≤ T) :
    C.DefinedUpTo T := by
  refine C.definedUpTo_of_locallyFinite (fun S => ?_) T hT
  rcases le_or_gt S 0 with hS | hS
  · have hempty : C.surgeryTimes ∩ Iic S = ∅ := by
      ext t
      simp only [mem_inter_iff, mem_Iic, mem_empty_iff_false, iff_false, not_and]
      intro ht htS
      exact absurd (lt_of_lt_of_le (hpos t ht) (le_trans htS hS)) (lt_irrefl 0)
    rw [hempty]
    exact Set.finite_empty
  · have hfin := (prof S hS).surgeryTimes_finite hS.le
    rw [hprof S hS] at hfin
    exact hfin.subset (fun t ht => ⟨ht.1, hpos t ht.1, ht.2⟩)
