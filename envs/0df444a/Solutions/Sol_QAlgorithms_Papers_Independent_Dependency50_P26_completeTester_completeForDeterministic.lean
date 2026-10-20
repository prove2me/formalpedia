-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P26.completeTester_completeForDeterministic
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:44:25.017896+00:00
-- url     : https://prove2.me/submissions/7dd5ff29-f729-4a88-8d8d-2b5ab17443dd

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P26

/-- PDF p.20, paragraph after Definition 14: completeness implies completeness on D. -/
theorem solution (s : Signature) (n k : ℕ)
    (P : Fin k → Matrix (Basis s n) (Basis s n) ℂ)
    (hP : CombTester s n k P) (hic : InformationallyComplete P) :
    CompleteForDeterministic s n k P := by
  intro X _
  exact hic X


end

