-- Prove2me | solution 1 for Orthonormal.hasSum_inner_smul_map_of_map_eq_zero_of_forall_inner_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/7152cea0-6318-552c-96d9-8e2980dabfd6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Orthonormal_hasSum_inner_smul_map_of_map_eq_zero_of_forall_inner_eq_zero

set_option autoImplicit false

open scoped InnerProductSpace

namespace OrthoExpand

theorem main
    {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {ι : Type*} (b : ι → E) (hb : Orthonormal 𝕜 b) (T : E →L[𝕜] F)
    (hT : ∀ v : E, (∀ i, ⟪b i, v⟫_𝕜 = 0) → T v = 0) (u : E) :
    HasSum (fun i => ⟪b i, u⟫_𝕜 • T (b i)) (T u) := by
  classical
  set V : Submodule 𝕜 E := (Submodule.span 𝕜 (Set.range b)).topologicalClosure with hV
  have hVc : IsClosed (V : Set E) := Submodule.isClosed_topologicalClosure _
  haveI : CompleteSpace V := hVc.completeSpace_coe
  have hmem : ∀ i, b i ∈ V := fun i =>
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)
  set b' : ι → V := fun i => ⟨b i, hmem i⟩ with hb'
  have hb'o : Orthonormal 𝕜 b' := by
    rw [orthonormal_iff_ite] at hb ⊢
    intro i j
    rw [Submodule.coe_inner]
    exact hb i j

  have hdense : ⊤ ≤ (Submodule.span 𝕜 (Set.range b')).topologicalClosure := by
    intro x _
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
      Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, Set.mem_preimage]
    have hrange : (V.subtype : V → E) '' Set.range b' = Set.range b := by
      ext y
      simp only [Set.mem_image, Set.mem_range, Submodule.subtype_apply]
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩; exact ⟨b' i, ⟨i, rfl⟩, rfl⟩
    have hmap : (Submodule.span 𝕜 (Set.range b')).map V.subtype = Submodule.span 𝕜 (Set.range b) := by
      rw [Submodule.map_span, hrange]
    have himg : ((↑) : V → E) '' (Submodule.span 𝕜 (Set.range b') : Set V) = (Submodule.span 𝕜 (Set.range b) : Set E) := by
      rw [← hmap, Submodule.map_coe]
      rfl
    rw [himg, ← Submodule.topologicalClosure_coe]
    exact x.2
  set B : HilbertBasis ι 𝕜 V := HilbertBasis.mk hb'o hdense with hB
  have hBcoe : ∀ i, ((B i : V) : E) = b i := fun i => by
    rw [hB, HilbertBasis.coe_mk]

  have h1 : HasSum (fun i => ⟪((B i : V) : E), u⟫_𝕜 • B i) (V.orthogonalProjection u) :=
    B.hasSum_orthogonalProjection u

  have h2 := (T.comp V.subtypeL).hasSum h1
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, Submodule.subtypeL_apply,
    map_smul, hBcoe] at h2

  have h3 : T u = T ((V.orthogonalProjection u : V) : E) := by
    have hperp : ∀ i, ⟪b i, u - ((V.orthogonalProjection u : V) : E)⟫_𝕜 = 0 := by
      intro i
      rw [inner_eq_zero_symm]
      have := Submodule.starProjection_inner_eq_zero (K := V) u (b i) (hmem i)
      rwa [Submodule.starProjection_apply] at this
    have := hT _ hperp
    rw [map_sub, sub_eq_zero] at this
    exact this
  rw [h3]
  convert h2 using 1

end OrthoExpand

theorem solution
    {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {ι : Type*} (b : ι → E) (hb : Orthonormal 𝕜 b) (T : E →L[𝕜] F)
    (hT : ∀ v : E, (∀ i, ⟪b i, v⟫_𝕜 = 0) → T v = 0) (u : E) :
    HasSum (fun i => ⟪b i, u⟫_𝕜 • T (b i)) (T u) :=
  OrthoExpand.main b hb T hT u

end S_Orthonormal_hasSum_inner_smul_map_of_map_eq_zero_of_forall_inner_eq_zero
end P2MW
export P2MW.S_Orthonormal_hasSum_inner_smul_map_of_map_eq_zero_of_forall_inner_eq_zero (solution)
