-- Prove2me | solution 1 for ThreeSum.TernaryPairedPotential.mod_independent_of_minorWeight_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:16:21.457139+00:00
-- url     : https://prove2.me/submissions/85cde893-a501-4629-8c33-17913795dfa2

import Definitions.Def_Submission_ThreeSum_TernaryPairedSupport
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformRank
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.Data.ZMod.Basic
import Definitions.Def_Submission_ThreeSum_TernaryCoverOutputCap
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Definitions.Def_Submission_ThreeSum_TernaryPairedPotential
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_mapEdge_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_output_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_reindex_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_swapEdge_swapEdge
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.mapEdge_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.output_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.reindex_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.swapEdge_swapEdge



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedPotential
open Finset Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {K : Type*} [Field K] [DecidableEq K]
namespace ThreeSum.TernaryPairedPotential
theorem _root_.solution {d Λ p : ℕ} [Fact p.Prime]
    (A : Matrix (Fin d) (Fin Λ) ℤ) (hw : 0 < minorWeight A)
    (hsmall : ∀ f : Fin d → Fin Λ, (A.submatrix id f).det.natAbs < p) :
    LinearIndependent (ZMod p) (fun i j => (A i j : ZMod p)) := by
  obtain ⟨f,hf,hpos⟩ := sum_pos_iff.mp hw
  have hd : (A.submatrix id f).det ≠ 0 := by
    intro hz
    simp [hz] at hpos
  have hm : (((Int.castRingHom (ZMod p)).mapMatrix (A.submatrix id f)).det) ≠ 0 := by
    intro hz
    have he := (Int.castRingHom (ZMod p)).map_det (A.submatrix id f)
    rw [hz] at he
    have hdvd : (p : ℤ) ∣ (A.submatrix id f).det :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp he
    exact hd (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd (by simpa using hsmall f))
  have hi := Matrix.linearIndependent_row_iff.mpr (Matrix.nonsingular_iff_det_ne_zero.mpr hm)
  let restrict : (Fin Λ → ZMod p) →ₗ[ZMod p] (Fin d → ZMod p) :=
    LinearMap.pi fun i => LinearMap.proj (f i)
  exact LinearIndependent.of_comp restrict hi
end ThreeSum.TernaryPairedPotential
