-- Prove2me | solution 1 for ROLDescent.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T16:10:00.865233+00:00
-- url     : https://prove2.me/submissions/2f3da6ed-f4dc-4913-bc77-06e1087c0b90

import Mathlib
import Definitions.Def_ROLDescent_sumMap

set_option autoImplicit false

namespace ROLDescent.GramProof

open ContinuousLinearMap

variable {ι : Type*} [Fintype ι]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  (U : ι → Submodule ℂ H)

theorem sumMap_apply (u : PiLp 2 (fun i => ↥(U i))) :
    sumMap U u = ∑ i, ((u i : U i) : H) := by
  simp [sumMap]

theorem sumMap_adjoint_apply (x : H) :
    adjoint (sumMap U) x = WithLp.toLp 2 (fun i => (U i).orthogonalProjectionOnto x) := by
  apply ext_inner_right ℂ
  intro u
  rw [adjoint_inner_left, sumMap_apply, inner_sum, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp

theorem sumMap_comp_adjoint :
    sumMap U ∘L adjoint (sumMap U) = ∑ i, (U i).starProjection := by
  ext x
  change sumMap U (adjoint (sumMap U) x) = (∑ i, (U i).starProjection) x
  rw [sumMap_apply, sumMap_adjoint_apply]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rfl

end ROLDescent.GramProof

namespace ROLDescent

theorem lemma_2_3_proof {ι : Type*} [Fintype ι]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (U : ι → Submodule ℂ H) :
    (∀ i, (U i).subtypeL ∘L ContinuousLinearMap.adjoint (U i).subtypeL = (U i).starProjection) ∧
    (ContinuousLinearMap.adjoint (sumMap U) ∘L sumMap U).IsPositive ∧
    ‖ContinuousLinearMap.adjoint (sumMap U) ∘L sumMap U‖ = ‖sumMap U‖ ^ 2 ∧
    ‖sumMap U‖ ^ 2 = ‖∑ i, (U i).starProjection‖ ∧
    (∀ u : PiLp 2 (fun i => ↥(U i)),
      ‖∑ i, ((u i : ↥(U i)) : H)‖ ^ 2 ≤
        ‖ContinuousLinearMap.adjoint (sumMap U) ∘L sumMap U‖ * ∑ i, ‖u i‖ ^ 2) := by
  have hnorm : ‖ContinuousLinearMap.adjoint (sumMap U) ∘L sumMap U‖ =
      ‖sumMap U‖ ^ 2 := by
    simpa only [pow_two] using ContinuousLinearMap.norm_adjoint_comp_self (sumMap U)
  refine ⟨?_, (sumMap U).isPositive_adjoint_comp_self, hnorm, ?_, ?_⟩
  · intro i
    rw [Submodule.adjoint_subtypeL]
    rfl
  · calc
      ‖sumMap U‖ ^ 2 = ‖sumMap U ∘L ContinuousLinearMap.adjoint (sumMap U)‖ := by
        simpa only [ContinuousLinearMap.adjoint_adjoint, LinearIsometryEquiv.norm_map,
          pow_two] using
          (ContinuousLinearMap.norm_adjoint_comp_self (ContinuousLinearMap.adjoint (sumMap U))).symm
      _ = ‖∑ i, (U i).starProjection‖ := by rw [GramProof.sumMap_comp_adjoint]
  · intro u
    calc
      ‖∑ i, ((u i : U i) : H)‖ ^ 2 = ‖sumMap U u‖ ^ 2 := by
        rw [GramProof.sumMap_apply]
      _ ≤ (‖sumMap U‖ * ‖u‖) ^ 2 := by
        gcongr
        exact (sumMap U).le_opNorm u
      _ = ‖ContinuousLinearMap.adjoint (sumMap U) ∘L sumMap U‖ * ∑ i, ‖u i‖ ^ 2 := by
        rw [hnorm, mul_pow, PiLp.norm_sq_eq_of_L2]

end ROLDescent

#print axioms ROLDescent.lemma_2_3_proof

open ROLDescent
theorem solution {ι : Type*} [Fintype ι]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (U : ι → Submodule ℂ H) :
    (∀ i, (U i).subtypeL ∘L ContinuousLinearMap.adjoint (U i).subtypeL = (U i).starProjection) ∧
    (ContinuousLinearMap.adjoint (sumMap U) ∘L sumMap U).IsPositive ∧
    ‖ContinuousLinearMap.adjoint (sumMap U) ∘L sumMap U‖ = ‖sumMap U‖ ^ 2 ∧
    ‖sumMap U‖ ^ 2 = ‖∑ i, (U i).starProjection‖ ∧
    (∀ u : PiLp 2 (fun i => ↥(U i)),
      ‖∑ i, ((u i : ↥(U i)) : H)‖ ^ 2 ≤
        ‖ContinuousLinearMap.adjoint (sumMap U) ∘L sumMap U‖ * ∑ i, ‖u i‖ ^ 2) :=
  ROLDescent.lemma_2_3_proof U

#print axioms solution
