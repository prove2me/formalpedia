-- Prove2me | solution 1 for ROLDescent.eq_74_consequences
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T16:10:00.885763+00:00
-- url     : https://prove2.me/submissions/4591fa1a-948e-4116-88f6-a5be5b571116

import Mathlib
import Definitions.Def_ROLDescent_IsSubspaceHierarchy

set_option autoImplicit false

namespace ROLDescent.ProjectionProof

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [FiniteDimensional ℂ K]

theorem projection_difference (A B : Submodule ℂ K) (h : B ≤ A) :
    A.starProjection - B.starProjection = (A ⊓ Bᗮ).starProjection := by
  ext x
  have hBA : B.starProjection (A.starProjection x) = B.starProjection x := by
    exact congrArg (fun f : K →L[ℂ] K => f x)
      (Submodule.starProjection_comp_starProjection_of_le h)
  have hmem : A.starProjection x - B.starProjection x ∈ A ⊓ Bᗮ := by
    refine ⟨A.sub_mem (A.starProjection_apply_mem x) (h (B.starProjection_apply_mem x)), ?_⟩
    change A.starProjection x - B.starProjection x ∈ (Bᗮ : Submodule ℂ K)
    rw [← hBA]
    exact B.sub_starProjection_mem_orthogonal (A.starProjection x)
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hmem
  intro y hy
  rw [show x - (A.starProjection x - B.starProjection x) =
      (x - A.starProjection x) + B.starProjection x by abel, inner_add_left]
  rw [A.starProjection_inner_eq_zero x y hy.1,
    hy.2 _ (B.starProjection_apply_mem x), add_zero]

end ROLDescent.ProjectionProof

namespace ROLDescent

theorem eq_74_consequences_proof {V : Type*} [Fintype V] [DecidableEq V]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]
    (X : Finset (Finset V)) (d : ℕ) (I : Finset V → Submodule ℂ K)
    (hI : IsSubspaceHierarchy X d I) (τ : Finset V) (hτ : τ ∈ X) (hτd : τ.card + 2 ≤ d) :
    (∀ i ∈ HDXConc.linkVerts X τ,
      I (insert i τ) ⊔ (I τ ⊓ (I (insert i τ))ᗮ) = I τ ∧
      I (insert i τ) ⟂ (I τ ⊓ (I (insert i τ))ᗮ) ∧
      (I τ).starProjection - (I (insert i τ)).starProjection =
        (I τ ⊓ (I (insert i τ))ᗮ).starProjection) ∧
    I τ ⊓ (⨅ i ∈ HDXConc.linkVerts X τ, I τ ⊓ (I (insert i τ))ᗮ) = ⊥ := by
  obtain ⟨hnest, hspan⟩ := hI τ hτ hτd
  constructor
  · intro i hi
    refine ⟨?_, (Submodule.isOrtho_orthogonal_right _).mono_right inf_le_right,
      ProjectionProof.projection_difference _ _ (hnest i hi)⟩
    simpa only [inf_comm] using
      Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection (hnest i hi)
  · apply le_antisymm ?_ bot_le
    intro x hx
    have horth : x ∈ (I τ)ᗮ := by
      rw [← hspan, ← Submodule.iInf_orthogonal]
      refine (Submodule.mem_iInf _).mpr fun i => ?_
      by_cases hi : i ∈ HDXConc.linkVerts X τ
      · rw [iSup_pos hi]
        exact ((Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hx.2 i) hi).2
      · simp [hi]
    have hz : x = 0 := inner_self_eq_zero.mp (horth x hx.1)
    simpa only [Submodule.mem_bot] using hz

end ROLDescent

#print axioms ROLDescent.eq_74_consequences_proof

open ROLDescent
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]
    (X : Finset (Finset V)) (d : ℕ) (I : Finset V → Submodule ℂ K)
    (hI : IsSubspaceHierarchy X d I) (τ : Finset V) (hτ : τ ∈ X) (hτd : τ.card + 2 ≤ d) :
    (∀ i ∈ HDXConc.linkVerts X τ,
      I (insert i τ) ⊔ (I τ ⊓ (I (insert i τ))ᗮ) = I τ ∧
      I (insert i τ) ⟂ (I τ ⊓ (I (insert i τ))ᗮ) ∧
      (I τ).starProjection - (I (insert i τ)).starProjection =
        (I τ ⊓ (I (insert i τ))ᗮ).starProjection) ∧
    I τ ⊓ (⨅ i ∈ HDXConc.linkVerts X τ, I τ ⊓ (I (insert i τ))ᗮ) = ⊥ :=
  ROLDescent.eq_74_consequences_proof X d I hI τ hτ hτd

#print axioms solution
