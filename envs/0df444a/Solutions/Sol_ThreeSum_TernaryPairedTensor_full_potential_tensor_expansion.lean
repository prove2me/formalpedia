-- Prove2me | solution 1 for ThreeSum.TernaryPairedTensor.full_potential_tensor_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:49:40.472209+00:00
-- url     : https://prove2.me/submissions/c196e4dc-a8d2-443e-8681-85ddef31e71b

import Definitions.Def_Submission_ThreeSum_TernaryPairedSupportConcrete
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensor
import Theorems.Thm_ThreeSum_TernaryPairedTensor_tuple_sum_tensor_expansion
import Theorems.Thm_ThreeSum_TernaryPairedTensor_rowWeight_intCast
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
theorem _root_.solution {m Λ : ℕ} (L R' : P → Fin Λ → ℤ) :
    ((∑ e : Fin m → P, rowWeight (Sum.elim (fun i => L (e i)) (fun i => R' (e i)))) : ℤ) =
      ∑ cols : PairedIndex m → Fin Λ,
      ∑ σ : Equiv.Perm (PairedIndex m), ∑ τ : Equiv.Perm (PairedIndex m),
        (((Equiv.Perm.sign σ : ℤ) : ℤ) * ((Equiv.Perm.sign τ : ℤ) : ℤ)) *
        ∏ i : Fin m, tensor L R' (cols (σ (.inl i))) (cols (τ (.inl i)))
          (cols (σ (.inr i))) (cols (τ (.inr i))) := by
  simp only [Nat.cast_sum,rowWeight_intCast]
  rw [sum_comm]
  apply sum_congr rfl
  intro cols hcols
  exact tuple_sum_tensor_expansion L R' cols
end ThreeSum.TernaryPairedTensor
