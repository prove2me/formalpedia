-- Prove2me | solution 1 for ThreeSum.TernaryPairedPotential.minor_small_of_entry_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:35:04.238845+00:00
-- url     : https://prove2.me/submissions/b28922ac-0722-4832-a761-01e67ef3f6de

import Definitions.Def_Submission_ThreeSum_TernaryPairedSupport
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformRank
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.Data.ZMod.Basic
import Definitions.Def_Submission_ThreeSum_TernaryCoverOutputCap
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Definitions.Def_Submission_ThreeSum_TernaryPairedPotential
import Theorems.Thm_ThreeSum_TernaryPairedPotential_minor_natAbs_le

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedPotential
open Finset Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {K : Type*} [Field K] [DecidableEq K]
namespace ThreeSum.TernaryPairedPotential
theorem _root_.solution {d Λ p : ℕ} (A : Matrix (Fin d) (Fin Λ) ℤ)
    (b : ℕ) (hA : ∀ i j, (A i j).natAbs ≤ b) (hp : d.factorial*b^d < p) :
    ∀ f : Fin d → Fin Λ, (A.submatrix id f).det.natAbs < p := by
  intro f
  exact (minor_natAbs_le A b hA f).trans_lt hp
end ThreeSum.TernaryPairedPotential
