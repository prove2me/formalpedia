-- Prove2me | solution 1 for RobustUncLP.Ellipsoidal.uncSet_eq_image_PFeas
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:17:29.973126+00:00
-- url     : https://prove2.me/submissions/e09b3d86-7852-4cde-b315-2b4690262cc3

import Mathlib
import Definitions.Def_RobustUncLP_Ellipsoidal_Setting
import Definitions.Def_RobustUncLP_Ellipsoidal_SystemC

open RobustUncLP.Ellipsoidal Matrix RobustUncLP.Ellipsoidal.EllipsoidalData in
theorem solution {m n k : ℕ} (D : EllipsoidalData m n k) :
    D.uncSet = (fun u => D.Pi 0 (u 0)) '' PFeas D := by
  ext A
  constructor
  · intro hA
    simp only [uncSet, Set.mem_iInter, ellipsoid, Set.mem_setOf_eq] at hA
    choose u hu1 hu2 using hA
    refine ⟨u, ⟨fun ℓ => ?_, hu2⟩, ?_⟩
    · rw [← hu1 ℓ, ← hu1 0]
    · exact (hu1 0).symm
  · rintro ⟨u, ⟨h1, h2⟩, rfl⟩
    simp only [uncSet, Set.mem_iInter, ellipsoid, Set.mem_setOf_eq]
    intro ℓ
    exact ⟨u ℓ, (h1 ℓ).symm, h2 ℓ⟩

