-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P40.no_cloning
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-31T00:28:33.507843+00:00
-- url     : https://prove2.me/submissions/ec88ad82-a517-42f0-be0a-3a0bb4b878cb

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P40
import Theorems.Thm_QAlgorithms_GottesmanIntro_noCloning

set_option autoImplicit false
open QAlgorithms

theorem solution (d : ℕ) (hd : 2 ≤ d) :
    ¬ ∃ T : Superop (Fin d) (Fin d × Fin d), IsChannel T ∧
      ∀ psi : EuclideanSpace ℂ (Fin d), ‖psi‖ = 1 →
        T (pureDensity psi) = Matrix.kronecker (pureDensity psi) (pureDensity psi) := by
  rintro ⟨T, hT, hc⟩
  apply GottesmanIntro.noCloning (by simpa using hd) T hT
  intro psi hpsi
  rw [hc psi hpsi]
  ext i j
  simp [pureDensity, tensorVec, Matrix.kronecker, Matrix.kroneckerMap, mul_mul_mul_comm]

