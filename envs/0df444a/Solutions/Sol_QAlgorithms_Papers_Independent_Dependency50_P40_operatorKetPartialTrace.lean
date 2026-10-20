-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P40.operatorKetPartialTrace
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:15:25.406605+00:00
-- url     : https://prove2.me/submissions/98100696-228c-44f6-819d-152603f58276

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P40

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P40

open scoped ComplexConjugate ComplexOrder Matrix

open QAlgorithms.Papers.Independent.Information100.P34 (dyad)

/-- PDF p.3, (12): tracing out the input factor of an operator-ket dyad. -/
theorem solution {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (C1 C2 : Matrix (Fin k) (Fin h) ℂ) :
    traceRight (dyad (operatorKet C1) (operatorKet C2)) = C1 * C2ᴴ := by
  ext i j
  simp [traceRight, dyad, operatorKet, Matrix.mul_apply]


end

