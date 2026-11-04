-- Prove2me | solution 1 for ThreeSum.TernaryPairedPotential.exists_nonsingular_column_selection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:35:02.830774+00:00
-- url     : https://prove2.me/submissions/208472a6-dd6d-4bc1-9435-18ef509ed6f3

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
import Theorems.Thm_ThreeSum_TernaryCoverUniformRank_row_rank_eq_column_rank
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
theorem _root_.solution {d Λ : ℕ}
    (A : Matrix (Fin d) (Fin Λ) K) (hA : LinearIndependent K A) :
    ∃ f : Fin d → Fin Λ, (A.submatrix id f).det ≠ 0 := by
  have hdim : Module.finrank K (Submodule.span K (Set.range fun j => fun i => A i j)) = d := by
    have he := TernaryCoverUniformRank.row_rank_eq_column_rank (fun i j => A i j)
    have hr : Module.finrank K (Submodule.span K (Set.range fun i => fun j => A i j)) = d := by
      simpa using finrank_span_eq_card hA
    exact he.symm.trans hr
  have hex : ∃ f : Fin d → Fin d → K,
      (∀ i, f i ∈ Set.range (fun j => fun i => A i j)) ∧
      Submodule.span K (Set.range f) =
        Submodule.span K (Set.range (fun j => fun i => A i j)) ∧ LinearIndependent K f := by
    have hh := Submodule.exists_fun_fin_finrank_span_eq K
      (Set.range (fun j => fun i => A i j))
    rw [hdim] at hh
    exact hh
  obtain ⟨f,hf,hspan,hind⟩ := hex
  let pick : Fin d → Fin Λ := fun i => Classical.choose (hf i)
  have hpick (i : Fin d) : (fun j => A j (pick i)) = f i := Classical.choose_spec (hf i)
  refine ⟨pick, Matrix.nonsingular_iff_det_ne_zero.mp
    (Matrix.linearIndependent_col_iff.mp ?_)⟩
  have he : (A.submatrix id pick).col = f := by
    funext i j
    exact congrFun (hpick i) j
  rw [he]
  exact hind
end ThreeSum.TernaryPairedPotential
