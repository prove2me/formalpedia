-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_pairNum_pushExpansion_bef8f5d6e996
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:39:49.087666+00:00
-- url     : https://prove2.me/submissions/6c0ed70a-db56-4d3a-a4ff-ad4c43959663

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_rename_vars_c54e0d859ef5

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
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {n n' : ℕ} (σ : Fin n → Fin n') (P : Ideal (MRing ι O))
    (x x' : Fin n' → K → ℤ) (f g : Fin n' → MRing ι O)
    (Gs : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ) (Q : List (K → ℤ)) :
    pairNum P x x' f g (pushExpansion σ Gs) Q =
      pairNum P (x ∘ σ) (x' ∘ σ) (f ∘ σ) (g ∘ σ) Gs Q := by
  have hcls : Sum.elim x x' ∘ Sum.map σ σ = Sum.elim (x ∘ σ) (x' ∘ σ) := by
    funext s
    cases s <;> rfl
  unfold pairNum pushExpansion
  have h1 : ∀ j, cycEval (fun (W : Ideal (MRing ι O)) => classNum (Sum.elim x x')
        (∑ i ∈ Finset.univ.filter (fun i => σ i = j), rename (Sum.map σ σ) (Gs i)) Q W)
        (ratDiv P (f j) (g j)) =
      ∑ i ∈ Finset.univ.filter (fun i => σ i = j),
        cycEval (fun (W : Ideal (MRing ι O)) => classNum (Sum.elim (x ∘ σ) (x' ∘ σ)) (Gs i) Q W)
          (ratDiv P (f (σ i)) (g (σ i))) := by
    intro j
    have hsum : ∀ W : Ideal (MRing ι O), classNum (Sum.elim x x')
        (∑ i ∈ Finset.univ.filter (fun i => σ i = j), rename (Sum.map σ σ) (Gs i)) Q W =
        ∑ i ∈ Finset.univ.filter (fun i => σ i = j),
          classNum (Sum.elim (x ∘ σ) (x' ∘ σ)) (Gs i) Q W := by
      intro W
      have := map_sum (classNumAddHom (Sum.elim x x') Q W)
        (fun i => rename (Sum.map σ σ) (Gs i)) (Finset.univ.filter (fun i => σ i = j))
      simp only [classNumAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
      rw [this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [classNum_rename_vars, hcls]
    simp only [hsum]
    rw [cycEval_eq_sum (ratDiv_finite_support P (f j) (g j))]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.mp hi).2, cycEval_eq_sum (ratDiv_finite_support P (f j) (g j))]
  simp only [h1]
  exact Finset.sum_fiberwise Finset.univ σ
    (fun i => cycEval (fun (W : Ideal (MRing ι O)) => classNum (Sum.elim (x ∘ σ) (x' ∘ σ)) (Gs i) Q W)
      (ratDiv P (f (σ i)) (g (σ i))))
end GroundTheory.Heights₂.Heights.NumbersDVR
