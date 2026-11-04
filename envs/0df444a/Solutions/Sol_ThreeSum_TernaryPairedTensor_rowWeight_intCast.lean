-- Prove2me | solution 1 for ThreeSum.TernaryPairedTensor.rowWeight_intCast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:39:54.24971+00:00
-- url     : https://prove2.me/submissions/d2397c6a-344f-423f-b0d6-a383b874aafc

import Definitions.Def_Submission_ThreeSum_TernaryPairedSupportConcrete
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensor
import Theorems.Thm_ThreeSum_TernaryPairedTensor_minorWeight_intCast
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
open ThreeSum ThreeSum.TernaryPairedTensor
open Finset Matrix TernaryPairedPotential
open scoped BigOperators
variable {P I R : Type*} [Fintype P] [CommRing R]
namespace ThreeSum.TernaryPairedTensor
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] {Λ : ℕ}
    (A : ι → Fin Λ → ℤ) :
    (rowWeight A : ℤ) = ∑ cols : ι → Fin Λ, (Matrix.det (fun i j => A i (cols j)))^2 := by
  let e := (Fintype.equivFin ι).symm
  let Φ := Equiv.arrowCongr e (Equiv.refl (Fin Λ))
  let M : Matrix (Fin (Fintype.card ι)) (Fin Λ) ℤ := fun i j => A (e i) j
  change (minorWeight M : ℤ) = _
  rw [minorWeight_intCast]
  calc
    _ = ∑ cols : Fin (Fintype.card ι) → Fin Λ,
        (Matrix.det (fun i j => A i (Φ cols j)))^2 := by
      apply sum_congr rfl
      intro cols hcols
      have hh := Matrix.det_submatrix_equiv_self e
        (fun i j => A i (Φ cols j))
      congr 1
      calc
        _ = (Matrix.submatrix (fun i j => A i (Φ cols j)) e e).det := by
          congr 1
          ext i j
          change A (e i) (cols j) = A (e i) (Φ cols (e j))
          simp [Φ,Equiv.arrowCongr]
        _ = _ := hh
    _ = _ := Φ.sum_comp (fun cols : ι → Fin Λ =>
      (Matrix.det (fun i j => A i (cols j)))^2)
end ThreeSum.TernaryPairedTensor
