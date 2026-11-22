-- Prove2me | solution 1 for VectorValuedHolomorphy.compactlySupportedTopology_t2_induced_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:01:25.008811+00:00
-- url     : https://prove2.me/submissions/7b6c3390-bb81-4fb7-8084-27acd63b7f5c

import Mathlib
import Definitions.Def_VectorValuedHolomorphy_CompactlySupportedInductiveLimit

open Filter Topology
open scoped CompactlySupported

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Sol_VectorValuedHolomorphy_compactlySupportedTopology_t2_induced_isClosed

open scoped ComplexOrder in
/-- The compact-open topology on continuous maps into a real or complex polynormable space is
polynormable. -/
theorem polynormableSpace_continuousMap (𝕜 X E : Type*) [RCLike 𝕜] [TopologicalSpace X]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] : PolynormableSpace 𝕜 C(X, E) := by
  letI : Module ℝ E := Module.restrictScalars ℝ 𝕜 E
  haveI : IsScalarTower ℝ 𝕜 E := IsScalarTower.restrictScalars ℝ 𝕜 E
  haveI : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  haveI : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms 𝕜 E).toLocallyConvexSpace
  haveI : LocallyConvexSpace 𝕜 E := LocallyConvexSpace.ofBasisZero 𝕜 E id _
    (LocallyConvexSpace.convex_basis_zero ℝ E)
    (fun _ h ↦ convex_RCLike_iff_convex_real.mpr h.2)
  infer_instance

end Sol_VectorValuedHolomorphy_compactlySupportedTopology_t2_induced_isClosed

open VectorValuedHolomorphy in
theorem solution (𝕜 : Type*) [RCLike 𝕜] (X : Type*)
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] (E : Type*) [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    [PolynormableSpace 𝕜 E] [T2Space E] :
    @T2Space C_c(X, E) (compactlySupportedTopology 𝕜 X E) ∧
    ∀ K : Set X, IsCompact K →
      TopologicalSpace.induced (Subtype.val : {f : C_c(X, E) // tsupport f ⊆ K} → C_c(X, E))
          (compactlySupportedTopology 𝕜 X E) =
        TopologicalSpace.induced (fun f : {f : C_c(X, E) // tsupport f ⊆ K} => (f.1 : C(X, E)))
          ContinuousMap.compactOpen ∧
      @IsClosed C_c(X, E) (compactlySupportedTopology 𝕜 X E) {f | tsupport f ⊆ K} := by
  letI τ : TopologicalSpace C_c(X, E) := compactlySupportedTopology 𝕜 X E
  have hW : WithSeminorms (compactlySupportedSeminormFamily 𝕜 X E) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup C_c(X, E) := hW.topologicalAddGroup
  haveI : PolynormableSpace 𝕜 C(X, E) :=
    Sol_VectorValuedHolomorphy_compactlySupportedTopology_t2_induced_isClosed.polynormableSpace_continuousMap
      𝕜 X E
  -- the linear inclusion `C_c(X, E) → C(X, E)`
  let ι : C_c(X, E) →ₗ[𝕜] C(X, E) :=
    { toFun := fun f => (f : C(X, E))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hι : Continuous ι := by
    refine (PolynormableSpace.withSeminorms 𝕜 C(X, E)).continuous_of_continuous_comp ι ?_
    intro p
    refine hW.continuous_seminorm ⟨p.1.comp ι, ?_⟩
    intro K _
    letI : TopologicalSpace {f : C_c(X, E) // tsupport f ⊆ K} :=
      TopologicalSpace.induced (fun f : {f : C_c(X, E) // tsupport f ⊆ K} => (f.1 : C(X, E)))
        ContinuousMap.compactOpen
    exact p.2.comp continuous_induced_dom
  have hinj : Function.Injective ι := fun f g h =>
    DFunLike.ext _ _ fun x => congrArg (fun u : C(X, E) => u x) h
  refine ⟨T2Space.of_injective_continuous hinj hι, fun K hK => ⟨?_, ?_⟩⟩
  · apply le_antisymm
    · rw [← continuous_iff_le_induced]
      exact hι.comp continuous_induced_dom
    · letI σ : TopologicalSpace {f : C_c(X, E) // tsupport f ⊆ K} :=
        TopologicalSpace.induced (fun f : {f : C_c(X, E) // tsupport f ⊆ K} => (f.1 : C(X, E)))
          ContinuousMap.compactOpen
      rw [← continuous_iff_le_induced]
      rw [continuous_iff_continuousAt]
      intro f₀
      rw [ContinuousAt, hW.tendsto_nhds]
      intro i ε hε
      have hsub : ∀ g : {f : C_c(X, E) // tsupport f ⊆ K}, tsupport ⇑(g.1 - f₀.1) ⊆ K := by
        intro g
        refine closure_minimal ?_ hK.isClosed
        rw [CompactlySupportedContinuousMap.coe_sub]
        refine (Function.support_sub _ _).trans (Set.union_subset ?_ ?_)
        · exact (subset_tsupport _).trans g.2
        · exact (subset_tsupport _).trans f₀.2
      let d : {f : C_c(X, E) // tsupport f ⊆ K} → {f : C_c(X, E) // tsupport f ⊆ K} :=
        fun g => ⟨g.1 - f₀.1, hsub g⟩
      have hd : Continuous d := by
        rw [continuous_induced_rng]
        exact (continuous_induced_dom (t := ContinuousMap.compactOpen)).sub continuous_const
      have hc : Continuous (fun g => i.1 (d g).1) := (i.2 K hK).comp hd
      have h0 : i.1 (d f₀).1 = 0 := by simp [d]
      have ht := hc.tendsto f₀
      rw [h0] at ht
      exact ht.eventually (gt_mem_nhds hε)
  · have hKc : IsClosed K := hK.isClosed
    have hset : {f : C_c(X, E) | tsupport f ⊆ K} = ⋂ x ∈ Kᶜ, {f : C_c(X, E) | f x = 0} := by
      ext f
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_compl_iff]
      rw [tsupport, hKc.closure_subset_iff, Function.support_subset_iff']
    have hev : ∀ x : X, Continuous fun f : C_c(X, E) => f x := fun x =>
      show Continuous ((fun g : C(X, E) => g x) ∘ ι) from (continuous_eval_const x).comp hι
    rw [hset]
    exact isClosed_biInter fun x _ => isClosed_eq (hev x) continuous_const
