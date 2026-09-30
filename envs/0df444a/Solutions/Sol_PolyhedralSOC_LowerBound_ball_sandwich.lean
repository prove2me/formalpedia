-- Prove2me | solution 1 for PolyhedralSOC.LowerBound.ball_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:24:55.648678+00:00
-- url     : https://prove2.me/submissions/c62b7d15-6c21-4431-8078-8ac94e20e60b

import Mathlib
import Definitions.Def_PolyhedralSOC_Shared_LorentzCone
import Definitions.Def_PolyhedralSOC_Shared_IsPolyhedralApprox
import Definitions.Def_PolyhedralSOC_LowerBound_ProofObjects
set_option autoImplicit false
open PolyhedralSOC PolyhedralSOC.LowerBound
theorem solution {k p q : ℕ} {ε : ℝ} (hε : 0 < ε)
    (P : (Fin k → ℝ) × ℝ × (Fin p → ℝ) →ₗ[ℝ] (Fin q → ℝ))
    (hP : Shared.IsPolyhedralApprox k p q ε P) :
    {y : Fin k → ℝ | Shared.eucNorm y ≤ 1} ⊆ sliceG P ∧
      sliceG P ⊆ {y : Fin k → ℝ | Shared.eucNorm y ≤ 1 + ε} := by
  constructor
  · intro y hy
    exact hP.1 y 1 hy
  · rintro y ⟨u, hu⟩
    simpa using hP.2 y 1 u hu
