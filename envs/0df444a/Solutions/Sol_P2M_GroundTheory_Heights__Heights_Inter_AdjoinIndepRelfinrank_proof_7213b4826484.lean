-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_AdjoinIndepRelfinrank_proof_7213b4826484
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:42.085846+00:00
-- url     : https://prove2.me/submissions/784544ea-54e9-4a0b-990f-17865aa1eff3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StAdjoinIndepRelfinrank
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PAdjoinIndepRelfinrank

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open IntermediateField IntermediateField.algebraAdjoinAdjoin Module
namespace GroundTheory.Heights₂.Heights.Inter
namespace AdjoinIndepRelfinrank
theorem _root_.solution : AdjoinIndepRelfinrank.Statement := by
  intro F Ω _ _ _ L₀ L ι t hle ht
  set L' : IntermediateField L₀ Ω := extendScalars hle with hL'
  set A : IntermediateField L₀ Ω := adjoin L₀ (Set.range t) with hA
  have ht' : AlgebraicIndependent L' t := ht

  let b := Module.Free.chooseBasis L₀ L'

  have hR : LinearIndependent (Algebra.adjoin L₀ (Set.range t)) (algebraMap L' Ω ∘ b) := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have hmem : ∀ j, ∃ p : MvPolynomial ι L₀, MvPolynomial.aeval t p = (g j : Ω) := fun j => by
      have : (g j : Ω) ∈ (MvPolynomial.aeval t : MvPolynomial ι L₀ →ₐ[L₀] Ω).range := by
        rw [← Algebra.adjoin_range_eq_range_aeval]
        exact (g j).2
      obtain ⟨p, hp⟩ := this
      exact ⟨p, hp⟩
    choose p hp using hmem
    set q : MvPolynomial ι L' :=
      ∑ j ∈ s, MvPolynomial.C (b j) * MvPolynomial.map (algebraMap L₀ L') (p j) with hq
    have hq0 : q = 0 := by
      apply ht'.eq_zero_of_aeval_eq_zero
      rw [hq, map_sum]
      rw [← hg]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_map_algebraMap, hp, Subalgebra.smul_def,
        Function.comp_apply, mul_comm]
      rfl
    have hcoef : ∀ m, ∀ j ∈ s, MvPolynomial.coeff m (p j) = 0 := by
      intro m
      have h := congrArg (MvPolynomial.coeff m) hq0
      rw [hq, MvPolynomial.coeff_sum, MvPolynomial.coeff_zero] at h
      simp only [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map] at h
      have hb := (linearIndependent_iff'.mp b.linearIndependent) s (fun j => MvPolynomial.coeff m (p j))
      apply hb
      rw [← h]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, mul_comm]
    have hpi : p i = 0 := MvPolynomial.ext _ _ fun m => hcoef m i hi
    apply Subtype.ext
    rw [← hp i, hpi, map_zero]
    rfl
  have hK : LinearIndependent A (algebraMap L' Ω ∘ b) :=
    (LinearIndependent.iff_fractionRing (Algebra.adjoin L₀ (Set.range t)) A).mp hR
  have hdisj : A.LinearDisjoint L' := LinearDisjoint.of_basis_right' b hK

  have hlow : A.restrictScalars F = L₀ ⊔ adjoin F (Set.range t) := by
    rw [hA, restrictScalars_adjoin_eq_sup]
  have hle' : A ≤ (adjoin L' (A : Set Ω)).restrictScalars L₀ := subset_adjoin L' (A : Set Ω)
  have hup : ((adjoin L' (A : Set Ω)).restrictScalars L₀).restrictScalars F =
      L ⊔ adjoin F (Set.range t) := by
    refine (restrictScalars_adjoin_eq_sup F L (A : Set Ω)).trans ?_
    have hAF : adjoin F (A : Set Ω) = L₀ ⊔ adjoin F (Set.range t) := by
      rw [← hlow]
      exact adjoin_self F (A.restrictScalars F)
    rw [hAF, ← sup_assoc, sup_eq_left.mpr hle]
  have hrel : IntermediateField.relfinrank (L₀ ⊔ adjoin F (Set.range t)) (L ⊔ adjoin F (Set.range t)) =
      finrank A (extendScalars hle') := by
    rw [← hlow, ← hup]
    exact relfinrank_eq_finrank_of_le hle'
  rw [hrel, relfinrank_eq_finrank_of_le hle]
  by_cases hfin : Module.Finite L₀ L'
  · have : Algebra.IsAlgebraic L₀ L' := Algebra.IsAlgebraic.of_finite L₀ L'
    have := hdisj.adjoin_rank_eq_rank_right_of_isAlgebraic_right
    exact congrArg Cardinal.toNat this
  · rw [finrank_of_not_finite hfin, finrank_of_not_finite]
    intro hfin'
    apply hfin
    let v : _ → extendScalars hle' := fun j => ⟨algebraMap L' Ω (b j), by
      exact IntermediateField.algebraMap_mem (adjoin L' (A : Set Ω)) (b j)⟩
    have hv : LinearIndependent A v := by
      apply LinearIndependent.of_comp (extendScalars hle').val.toLinearMap
      exact hK
    have := hv.finite_of_isNoetherian
    exact Module.Finite.of_basis b
end AdjoinIndepRelfinrank
end GroundTheory.Heights₂.Heights.Inter
