-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_isPairExpansion_push_f1807b2e66f9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:39.558728+00:00
-- url     : https://prove2.me/submissions/c98f05c3-9d2c-4b80-ae3c-d8da7991251d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {n n' m : ℕ} (σ : Fin n → Fin n') {A : MvPolynomial (Fin n) ℤ}
    {Gs : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ} (h : IsPairExpansion m A Gs) :
    IsPairExpansion m (rename σ A) (pushExpansion σ Gs) := by
  refine ⟨?_, fun j => IsHomogeneous.sum _ _ _ fun i _ => (h.homogeneous i).rename_isHomogeneous⟩
  have e1 : rename Sum.inl (rename σ A) = rename (Sum.map σ σ) (rename Sum.inl A) := by
    rw [rename_rename, rename_rename]
    rfl
  have e2 : rename Sum.inr (rename σ A) = rename (Sum.map σ σ) (rename Sum.inr A) := by
    rw [rename_rename, rename_rename]
    rfl
  rw [e1, e2, ← map_sub, h.expansion, map_sum]
  simp only [map_mul, map_sub, rename_X, Sum.map_inl, Sum.map_inr, pushExpansion, Finset.mul_sum]
  refine (Finset.sum_fiberwise Finset.univ σ _).symm.trans ?_
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i hi => ?_
  rw [(Finset.mem_filter.mp hi).2]
end GroundTheory.Heights₂.Heights.NumbersDVR
