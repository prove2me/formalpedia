-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMinorsBaseChange_proof_2557925af931
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:58:26.796994+00:00
-- url     : https://prove2.me/submissions/3a4d3608-631d-4634-8406-dcd62f82e583

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMinorsBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagMinorsBaseChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMinorsBaseChange_flagMinor_mul_const_mem_d361f6596ffb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMinorsBaseChange_exists_mul_eq_one_a97e11134c8a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
namespace FlagMinorsBaseChange
theorem _root_.solution : FlagMinorsBaseChange.Statement := by
  intro F _ n N1 B hB
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff]
    rintro _ ⟨q, rfl⟩
    exact FlagMinorsBaseChange.flagMinor_mul_const_mem (genMat F n) B _ (fun a b => rfl) q.1 q.2
  · obtain ⟨D, hD⟩ := FlagMinorsBaseChange.exists_mul_eq_one B hB
    have e : ∀ l b, ∑ k, B l k * D k b = (1 : Matrix (Fin n) (Fin n) F) l b := fun l b => by
      rw [← Matrix.mul_apply, hD]
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨q, rfl⟩
    refine FlagMinorsBaseChange.flagMinor_mul_const_mem _ D (genMat F n) ?_ q.1 q.2
    intro a b
    show X (a, b) = ∑ k, (∑ l, X (a, l) * C (B l k)) * C (D k b)
    symm
    simp_rw [Finset.sum_mul, mul_assoc, ← map_mul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, ← map_sum, e, Matrix.one_apply]
    simp
end FlagMinorsBaseChange
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
