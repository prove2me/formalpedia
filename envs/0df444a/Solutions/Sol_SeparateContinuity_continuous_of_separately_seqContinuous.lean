-- Prove2me | solution 1 for SeparateContinuity.continuous_of_separately_seqContinuous
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:13:49.540339+00:00
-- url     : https://prove2.me/submissions/92f7fd41-7c5d-4360-b971-c30b4bffae9d

import Mathlib

open Topology Filter
set_option autoImplicit false

namespace Sol_SeparateContinuity_continuous_of_separately_seqContinuous

/-- **Baire category lemma (the core of the Banach–Steinhaus argument).**
Let `E` be a Baire topological additive group, `G` a topological additive group and
`T m : E →+ G` a sequence of continuous additive maps which tends to `0` pointwise.
Then `T m (u m) → 0` for every null sequence `u` in `E`. -/
theorem tendsto_apply_of_pointwise_tendsto_zero {E G : Type*}
    [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [BaireSpace E]
    [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    (T : ℕ → E →+ G) (hT : ∀ m, Continuous (T m))
    (hpt : ∀ v : E, Tendsto (fun m => T m v) atTop (𝓝 0))
    (u : ℕ → E) (hu : Tendsto u atTop (𝓝 0)) :
    Tendsto (fun m => T m (u m)) atTop (𝓝 0) := by
  intro W hW
  -- neighbourhoods `V₁`, `V₂` of `0` in `G` with `V₁ - V₂ ⊆ W`
  have hsub : Tendsto (fun p : G × G => p.1 - p.2) (𝓝 ((0 : G), (0 : G))) (𝓝 (0 - 0)) :=
    (continuous_fst.sub continuous_snd).tendsto ((0 : G), (0 : G))
  rw [sub_zero] at hsub
  have hW' : {p : G × G | p.1 - p.2 ∈ W} ∈ 𝓝 ((0 : G), (0 : G)) := hsub hW
  rw [nhds_prod_eq, Filter.mem_prod_iff] at hW'
  obtain ⟨V₁, hV₁, V₂, hV₂, hV₁₂⟩ := hW'
  -- a closed neighbourhood `V ⊆ V₁ ∩ V₂` of `0` (a topological group is regular)
  obtain ⟨V, hV, hVclosed, hVsub⟩ :=
    exists_mem_nhds_isClosed_subset (Filter.inter_mem hV₁ hV₂)
  have hVV : ∀ a ∈ V, ∀ b ∈ V, a - b ∈ W := fun a ha b hb =>
    hV₁₂ (Set.mk_mem_prod (hVsub ha).1 (hVsub hb).2)
  -- the closed sets `C N = {v | ∀ m ≥ N, T m v ∈ V}` cover `E`
  let C : ℕ → Set E := fun N => ⋂ m, ⋂ (_ : N ≤ m), (T m) ⁻¹' V
  have hCclosed : ∀ N, IsClosed (C N) := fun N =>
    isClosed_iInter fun m => isClosed_iInter fun _ => hVclosed.preimage (hT m)
  have hCmem : ∀ N v, v ∈ C N ↔ ∀ m, N ≤ m → T m v ∈ V := by
    intro N v
    simp only [C, Set.mem_iInter, Set.mem_preimage]
  have hCcover : ⋃ N, C N = Set.univ := by
    refine Set.eq_univ_of_forall fun v => ?_
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((hpt v).eventually hV)
    exact Set.mem_iUnion.2 ⟨N, (hCmem N v).2 hN⟩
  -- Baire: some `C N` has an interior point `x₀`
  obtain ⟨N, x₀, hx₀⟩ := nonempty_interior_of_iUnion_of_closed hCclosed hCcover
  have hx₀C : x₀ ∈ C N := interior_subset hx₀
  have hnhds : interior (C N) ∈ 𝓝 x₀ := isOpen_interior.mem_nhds hx₀
  have htend : Tendsto (fun m => x₀ + u m) atTop (𝓝 x₀) := by
    have := (tendsto_const_nhds (x := x₀)).add hu
    rwa [add_zero] at this
  have hev : ∀ᶠ m in atTop, x₀ + u m ∈ interior (C N) := htend hnhds
  show ∀ᶠ m in atTop, T m (u m) ∈ W
  filter_upwards [hev, Filter.eventually_ge_atTop N] with m hm hNm
  have h1 : T m (x₀ + u m) ∈ V := (hCmem N _).1 (interior_subset hm) m hNm
  have h2 : T m x₀ ∈ V := (hCmem N _).1 hx₀C m hNm
  have h3 : T m (u m) = T m (x₀ + u m) - T m x₀ := by
    rw [map_add, add_sub_cancel_left]
  show T m (u m) ∈ W
  rw [h3]
  exact hVV _ h1 _ h2

/-- **Sequential joint continuity.**  A bilinear map `A : E × F → G` which is separately
sequentially continuous is sequentially continuous on `E × F`, as soon as `E` is a
completely metrizable topological vector space (no assumption on `F` and `G`). -/
theorem seqContinuous_of_separately_seqContinuous {𝕜 E F G : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [TopologicalSpace.IsCompletelyMetrizableSpace E]
    [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    (A : E →ₗ[𝕜] F →ₗ[𝕜] G)
    (h₁ : ∀ x : E, SeqContinuous (fun y : F => A x y))
    (h₂ : ∀ y : F, SeqContinuous (fun x : E => A x y)) :
    SeqContinuous (fun p : E × F => A p.1 p.2) := by
  -- `E` is metrizable, hence sequential: the partial maps `x ↦ A x y` are continuous
  have hcont : ∀ y : F, Continuous (fun x : E => A x y) := fun y => (h₂ y).continuous
  intro p q hp
  have hx : Tendsto (fun m => (p m).1) atTop (𝓝 q.1) :=
    (continuous_fst.tendsto q).comp hp
  have hy : Tendsto (fun m => (p m).2) atTop (𝓝 q.2) :=
    (continuous_snd.tendsto q).comp hp
  -- the null sequences `u m = x m - x` and `d m = y m - y`
  have hu : Tendsto (fun m => (p m).1 - q.1) atTop (𝓝 0) := by
    have := hx.sub (tendsto_const_nhds (x := q.1))
    rwa [sub_self] at this
  have hd : Tendsto (fun m => (p m).2 - q.2) atTop (𝓝 0) := by
    have := hy.sub (tendsto_const_nhds (x := q.2))
    rwa [sub_self] at this
  -- the continuous additive maps `T m = A (·) (d m)` tend to `0` pointwise
  let T : ℕ → E →+ G := fun m => (A.flip ((p m).2 - q.2)).toAddMonoidHom
  have hTcont : ∀ m, Continuous (T m) := fun m => hcont ((p m).2 - q.2)
  have hTpt : ∀ v : E, Tendsto (fun m => T m v) atTop (𝓝 0) := by
    intro v
    have h := h₁ v hd
    simp only [Function.comp_def, map_zero] at h
    exact h
  -- term 1: `A (x m - x) (y m - y) → 0` by the Baire category lemma
  have t1 : Tendsto (fun m => A ((p m).1 - q.1) ((p m).2 - q.2)) atTop (𝓝 0) :=
    tendsto_apply_of_pointwise_tendsto_zero T hTcont hTpt _ hu
  -- term 2: `A x (y m) → A x y`
  have t2 : Tendsto (fun m => A q.1 (p m).2) atTop (𝓝 (A q.1 q.2)) := h₁ q.1 hy
  -- term 3: `A (x m - x) y → 0`
  have t3 : Tendsto (fun m => A ((p m).1 - q.1) q.2) atTop (𝓝 0) := by
    have h := h₂ q.2 hu
    simpa only [Function.comp_def, map_zero, LinearMap.zero_apply] using h
  have hsum := (t1.add t2).add t3
  rw [zero_add, add_zero] at hsum
  refine hsum.congr fun m => ?_
  show A ((p m).1 - q.1) ((p m).2 - q.2) + A q.1 (p m).2 + A ((p m).1 - q.1) q.2
      = A (p m).1 (p m).2
  simp only [map_sub, LinearMap.sub_apply]
  abel

end Sol_SeparateContinuity_continuous_of_separately_seqContinuous

open Sol_SeparateContinuity_continuous_of_separately_seqContinuous in
theorem solution {𝕜 E F G : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [TopologicalSpace.IsCompletelyMetrizableSpace E]
    [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul 𝕜 F] [FirstCountableTopology F]
    [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [ContinuousSMul 𝕜 G]
    (A : E →ₗ[𝕜] F →ₗ[𝕜] G)
    (h₁ : ∀ x : E, SeqContinuous (fun y : F => A x y))
    (h₂ : ∀ y : F, SeqContinuous (fun x : E => A x y)) :
    Continuous (fun p : E × F => A p.1 p.2) := by
  -- `E` is metrizable, hence first countable; so is `F`; hence `E × F` is first countable
  have : FirstCountableTopology (E × F) := inferInstance
  -- a first countable space is sequential: sequential continuity is continuity
  have : SequentialSpace (E × F) := inferInstance
  exact (seqContinuous_of_separately_seqContinuous A h₁ h₂).continuous
