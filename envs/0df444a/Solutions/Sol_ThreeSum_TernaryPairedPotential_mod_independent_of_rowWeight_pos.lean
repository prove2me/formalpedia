-- Prove2me | solution 1 for ThreeSum.TernaryPairedPotential.mod_independent_of_rowWeight_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:29:55.995758+00:00
-- url     : https://prove2.me/submissions/dd8b8608-ad1b-4772-b4f1-08551508fd27

import Definitions.Def_Submission_ThreeSum_TernaryPairedSupport
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformRank
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.Data.ZMod.Basic
import Definitions.Def_Submission_ThreeSum_TernaryCoverOutputCap
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Definitions.Def_Submission_ThreeSum_TernaryPairedPotential
import Theorems.Thm_ThreeSum_TernaryPairedPotential_mod_independent_of_minorWeight_pos
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
theorem _root_.solution {ι : Type*} [Fintype ι] {Λ p : ℕ} [Fact p.Prime]
    (A : ι → Fin Λ → ℤ) (hw : 0 < rowWeight A)
    (hsmall : ∀ f : Fin (Fintype.card ι) → Fin Λ,
      (Matrix.submatrix (fun i => A ((Fintype.equivFin ι).symm i)) id f).det.natAbs < p) :
    LinearIndependent (ZMod p) (fun i j => (A i j : ZMod p)) := by
  have hh := mod_independent_of_minorWeight_pos
    (fun i => A ((Fintype.equivFin ι).symm i)) hw hsmall
  have hc := hh.comp (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  simpa only [Function.comp_def,Equiv.symm_apply_apply] using hc
end ThreeSum.TernaryPairedPotential
