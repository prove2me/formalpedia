-- Prove2me | solution 1 for ThreeSum.LightMomentZeroDetector.atoms_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:45:22.161525+00:00
-- url     : https://prove2.me/submissions/885f1593-b5d2-432c-a58b-fe7d9b12d6fe

import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_ThreeSum_LightMomentZeroDetector

set_option autoImplicit false
open ThreeSum ThreeSum.LightMomentZeroDetector
open Light ThreeSum.LightMomentDeterminant ThreeSum.LightFixedArithmetic
open FiniteMomentZeroDetector
namespace ThreeSum.LightMomentZeroDetector
theorem _root_.solution (H base : ℕ) (a : ℤ) (μ : ℕ → ℤ) :
    (atoms H 0).val ⟨frame [base,a],μ⟩=a := by rfl
end ThreeSum.LightMomentZeroDetector
