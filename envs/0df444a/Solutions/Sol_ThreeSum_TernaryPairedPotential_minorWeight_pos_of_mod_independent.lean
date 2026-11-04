-- Prove2me | solution 1 for ThreeSum.TernaryPairedPotential.minorWeight_pos_of_mod_independent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:39:15.129284+00:00
-- url     : https://prove2.me/submissions/409af003-07ba-4e26-869e-e0833e45c252

import Definitions.Def_Submission_ThreeSum_TernaryPairedSupport
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformRank
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.Data.ZMod.Basic
import Definitions.Def_Submission_ThreeSum_TernaryCoverOutputCap
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Definitions.Def_Submission_ThreeSum_TernaryPairedPotential
import Theorems.Thm_ThreeSum_TernaryPairedPotential_exists_nonsingular_column_selection

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedPotential
open Finset Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {K : Type*} [Field K] [DecidableEq K]
namespace ThreeSum.TernaryPairedPotential
theorem _root_.solution {d Λ : ℕ}
    (A : Matrix (Fin d) (Fin Λ) ℤ) (ρ : ℤ →+* K)
    (hA : LinearIndependent K (fun i j => ρ (A i j))) :
    0 < minorWeight A := by
  obtain ⟨f,hf⟩ := exists_nonsingular_column_selection (fun i j => ρ (A i j)) hA
  have hd : (A.submatrix id f).det ≠ 0 := by
    intro hz
    apply hf
    have he := ρ.map_det (A.submatrix id f)
    change (ρ.mapMatrix (A.submatrix id f)).det = 0
    rw [← he,hz,map_zero]
  unfold minorWeight
  exact sum_pos_iff.mpr ⟨f,mem_univ _,pow_pos (Int.natAbs_pos.mpr hd) 2⟩
end ThreeSum.TernaryPairedPotential
