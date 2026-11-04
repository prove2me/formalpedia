-- Prove2me | solution 1 for ThreeSum.TernaryPairedPotential.rowWeight_pos_of_mod_independent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:43:33.15236+00:00
-- url     : https://prove2.me/submissions/5ea77197-3df4-43d8-87a0-f9935e9d62db

import Definitions.Def_Submission_ThreeSum_TernaryPairedSupport
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformRank
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.Data.ZMod.Basic
import Definitions.Def_Submission_ThreeSum_TernaryCoverOutputCap
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Definitions.Def_Submission_ThreeSum_TernaryPairedPotential
import Theorems.Thm_ThreeSum_TernaryPairedPotential_minorWeight_pos_of_mod_independent

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedPotential
open Finset Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {K : Type*} [Field K] [DecidableEq K]
namespace ThreeSum.TernaryPairedPotential
theorem _root_.solution {ι : Type*} [Fintype ι] {Λ : ℕ}
    (A : ι → Fin Λ → ℤ) (ρ : ℤ →+* K)
    (hA : LinearIndependent K (fun i j => ρ (A i j))) : 0 < rowWeight A := by
  exact minorWeight_pos_of_mod_independent _ ρ
    (hA.comp (Fintype.equivFin ι).symm (Fintype.equivFin ι).symm.injective)
end ThreeSum.TernaryPairedPotential
