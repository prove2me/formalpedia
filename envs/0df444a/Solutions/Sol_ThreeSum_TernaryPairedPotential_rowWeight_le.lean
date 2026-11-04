-- Prove2me | solution 1 for ThreeSum.TernaryPairedPotential.rowWeight_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:35:40.053202+00:00
-- url     : https://prove2.me/submissions/7e1b8f4b-0768-404e-82b7-0d58a4f5a5df

import Definitions.Def_Submission_ThreeSum_TernaryPairedSupport
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformRank
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.Data.ZMod.Basic
import Definitions.Def_Submission_ThreeSum_TernaryCoverOutputCap
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Definitions.Def_Submission_ThreeSum_TernaryPairedPotential
import Theorems.Thm_ThreeSum_TernaryPairedPotential_minorWeight_le

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedPotential
open Finset Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {K : Type*} [Field K] [DecidableEq K]
namespace ThreeSum.TernaryPairedPotential
theorem _root_.solution {ι : Type*} [Fintype ι] {Λ : ℕ}
    (A : ι → Fin Λ → ℤ) (b : ℕ) (hA : ∀ i j, (A i j).natAbs ≤ b) :
    rowWeight A ≤ Λ^(Fintype.card ι)*((Fintype.card ι).factorial*b^(Fintype.card ι))^2 :=
  minorWeight_le _ b (fun i j => hA _ _)
end ThreeSum.TernaryPairedPotential
