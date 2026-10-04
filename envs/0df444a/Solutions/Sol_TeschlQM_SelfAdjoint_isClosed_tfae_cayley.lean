-- Prove2me | solution 1 for TeschlQM.SelfAdjoint.isClosed_tfae_cayley
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:57:04.184313+00:00
-- url     : https://prove2.me/submissions/b8268d0c-7a0d-4a7a-9d00-aa93b346e4f6

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_SelfAdjoint_IsCayleyTransform

open Filter Topology
open scoped InnerProductSpace

namespace TeschlQM.SelfAdjoint

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A subspace `S` of a complete space is closed iff its image under a continuous linear map
that is bounded below on `S` is closed. -/
lemma isClosed_iff_image_core {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (S : Submodule ℂ (H × H)) (T : (H × H) →L[ℂ] W) (hT : ∀ g ∈ S, ‖g‖ ≤ ‖T g‖) :
    IsClosed (S : Set (H × H)) ↔ IsClosed (T '' (S : Set (H × H))) := by
  constructor
  · intro hS
    refine IsSeqClosed.isClosed ?_
    intro w g' hw hlim
    choose g hg hTg using hw
    have hcauchy : CauchySeq g := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hlim.cauchySeq ε hε
      refine ⟨N, fun m hm k hk => ?_⟩
      have h1 := hT (g m - g k) (S.sub_mem (hg m) (hg k))
      rw [map_sub, hTg, hTg] at h1
      rw [dist_eq_norm]
      calc ‖g m - g k‖ ≤ ‖w m - w k‖ := h1
        _ = dist (w m) (w k) := (dist_eq_norm _ _).symm
        _ < ε := hN m hm k hk
    obtain ⟨g₀, hg₀⟩ := cauchySeq_tendsto_of_complete hcauchy
    have hg₀S : g₀ ∈ (S : Set (H × H)) := hS.mem_of_tendsto hg₀ (Eventually.of_forall hg)
    refine ⟨g₀, hg₀S, ?_⟩
    have h2 : Tendsto (fun n => T (g n)) atTop (𝓝 (T g₀)) := (T.continuous.tendsto g₀).comp hg₀
    simp_rw [hTg] at h2
    exact tendsto_nhds_unique h2 hlim
  · intro hI
    refine IsSeqClosed.isClosed ?_
    intro g g₀ hg hlim
    have h1 : Tendsto (fun n => T (g n)) atTop (𝓝 (T g₀)) := (T.continuous.tendsto g₀).comp hlim
    have hmem : T g₀ ∈ T '' (S : Set (H × H)) :=
      hI.mem_of_tendsto h1 (Eventually.of_forall fun n => ⟨g n, hg n, rfl⟩)
    obtain ⟨g', hg'S, hg'⟩ := hmem
    have h2 : Tendsto g atTop (𝓝 g') := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => hT (g n - g') (S.sub_mem (hg n) hg'S)) ?_
      have : (fun n => ‖T (g n - g')‖) = fun n => ‖T (g n) - T g₀‖ := by
        funext n; rw [map_sub, hg']
      rw [this]
      exact tendsto_iff_norm_sub_tendsto_zero.mp h1
    rw [tendsto_nhds_unique hlim h2]
    exact hg'S

/-- For symmetric `A`: `‖Aψ ± iψ‖² = ‖Aψ‖² + ‖ψ‖²`, hence both dominate `max ‖ψ‖ ‖Aψ‖`. -/
lemma norm_le_core (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (ψ : A.domain) :
    max ‖(ψ : H)‖ ‖A ψ‖ ≤ ‖A ψ + Complex.I • (ψ : H)‖ ∧
      max ‖(ψ : H)‖ ‖A ψ‖ ≤ ‖A ψ - Complex.I • (ψ : H)‖ := by
  have hre : RCLike.re (⟪A ψ, Complex.I • (ψ : H)⟫_ℂ) = 0 := by
    rw [inner_smul_right]
    have hsym : ⟪A ψ, (ψ : H)⟫_ℂ = ⟪(ψ : H), A ψ⟫_ℂ := (hA.2 ψ ψ).symm
    have hreal : (⟪A ψ, (ψ : H)⟫_ℂ).im = 0 := by
      have h := congrArg Complex.im hsym
      rw [← inner_conj_symm (A ψ) (ψ : H), Complex.conj_im] at h
      rw [hsym]; linarith
    simp [hreal]
  have h1 : ‖A ψ + Complex.I • (ψ : H)‖ ^ 2 = ‖A ψ‖ ^ 2 + ‖(ψ : H)‖ ^ 2 := by
    rw [norm_add_sq (𝕜 := ℂ), hre, norm_smul, Complex.norm_I, one_mul]; ring
  have h2 : ‖A ψ - Complex.I • (ψ : H)‖ ^ 2 = ‖A ψ‖ ^ 2 + ‖(ψ : H)‖ ^ 2 := by
    rw [norm_sub_sq (𝕜 := ℂ), hre, norm_smul, Complex.norm_I, one_mul]; ring
  have key : ∀ c : H, ‖c‖ ^ 2 = ‖A ψ‖ ^ 2 + ‖(ψ : H)‖ ^ 2 → max ‖(ψ : H)‖ ‖A ψ‖ ≤ ‖c‖ := by
    intro c hc
    refine max_le ?_ ?_
    · exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
        (by rw [hc]; nlinarith [sq_nonneg ‖A ψ‖])
    · exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
        (by rw [hc]; nlinarith [sq_nonneg ‖(ψ : H)‖])
  exact ⟨key _ h1, key _ h2⟩

/-- Elements of `Ran(A + i)`. -/
lemma mem_rangeAdd_I_core (A : H →ₗ.[ℂ] H) (x : H) :
    x ∈ rangeAdd A Complex.I ↔ ∃ ψ : A.domain, A ψ + Complex.I • (ψ : H) = x := by
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨⟨φ, φ.2⟩, ?_⟩
    rw [← hφ]
    show A ⟨φ, φ.2⟩ + Complex.I • (φ : H) = Complex.I • (φ : H) + A ⟨φ, φ.2⟩
    rw [add_comm]
  · rintro ⟨ψ, rfl⟩
    refine ⟨⟨ψ, ψ.2⟩, ?_⟩
    show Complex.I • (ψ : H) + A ψ = A ψ + Complex.I • (ψ : H)
    rw [add_comm]

end TeschlQM.SelfAdjoint

open TeschlQM.SelfAdjoint in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A V : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (hV : IsCayleyTransform A V) :
    List.TFAE [A.IsClosed, IsClosed (V.domain : Set H), IsClosed (Set.range V), V.IsClosed] := by
  obtain ⟨hVdom, hVapp⟩ := hV
  -- the three maps
  let T₁ : (H × H) →L[ℂ] H := ContinuousLinearMap.snd ℂ H H + Complex.I • ContinuousLinearMap.fst ℂ H H
  let T₂ : (H × H) →L[ℂ] H := ContinuousLinearMap.snd ℂ H H - Complex.I • ContinuousLinearMap.fst ℂ H H
  let T₃ : (H × H) →L[ℂ] H × H := T₁.prod T₂
  have hT₁ : ∀ g : H × H, T₁ g = g.2 + Complex.I • g.1 := fun g => by simp [T₁]
  have hT₂ : ∀ g : H × H, T₂ g = g.2 - Complex.I • g.1 := fun g => by simp [T₂]
  have hT₃ : ∀ g : H × H, T₃ g = (g.2 + Complex.I • g.1, g.2 - Complex.I • g.1) := fun g => by
    simp [T₃, hT₁, hT₂]
  -- graph elements
  have hgraph : ∀ g : H × H, g ∈ A.graph ↔ ∃ ψ : A.domain, ((ψ : H), A ψ) = g := by
    intro g
    rw [LinearPMap.mem_graph_iff]
    constructor
    · rintro ⟨ψ, h1, h2⟩; exact ⟨ψ, Prod.ext h1 h2⟩
    · rintro ⟨ψ, rfl⟩; exact ⟨ψ, rfl, rfl⟩
  -- norm bounds on the graph
  have hb₁ : ∀ g ∈ A.graph, ‖g‖ ≤ ‖T₁ g‖ := by
    intro g hg
    obtain ⟨ψ, rfl⟩ := (hgraph g).mp hg
    rw [hT₁, Prod.norm_def]
    exact (norm_le_core A hA ψ).1
  have hb₂ : ∀ g ∈ A.graph, ‖g‖ ≤ ‖T₂ g‖ := by
    intro g hg
    obtain ⟨ψ, rfl⟩ := (hgraph g).mp hg
    rw [hT₂, Prod.norm_def]
    exact (norm_le_core A hA ψ).2
  have hb₃ : ∀ g ∈ A.graph, ‖g‖ ≤ ‖T₃ g‖ := by
    intro g hg
    have := hb₁ g hg
    rw [hT₃, Prod.norm_def]
    rw [hT₁] at this
    exact this.trans (le_max_left _ _)
  -- the images
  have hI₁ : T₁ '' (A.graph : Set (H × H)) = (V.domain : Set H) := by
    ext x
    rw [hVdom]
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨ψ, rfl⟩ := (hgraph g).mp hg
      rw [hT₁]
      exact (mem_rangeAdd_I_core A _).mpr ⟨ψ, rfl⟩
    · intro hx
      obtain ⟨ψ, rfl⟩ := (mem_rangeAdd_I_core A x).mp hx
      exact ⟨((ψ : H), A ψ), (hgraph _).mpr ⟨ψ, rfl⟩, by rw [hT₁]⟩
  have hVmem : ∀ ψ : A.domain, A ψ + Complex.I • (ψ : H) ∈ V.domain := fun ψ => by
    rw [hVdom]; exact (mem_rangeAdd_I_core A _).mpr ⟨ψ, rfl⟩
  have hI₂ : T₂ '' (A.graph : Set (H × H)) = Set.range V := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨ψ, rfl⟩ := (hgraph g).mp hg
      rw [hT₂]
      exact ⟨⟨_, hVmem ψ⟩, hVapp ψ (hVmem ψ)⟩
    · rintro ⟨y, rfl⟩
      have hy : (y : H) ∈ rangeAdd A Complex.I := by rw [← hVdom]; exact y.2
      obtain ⟨ψ, hψ⟩ := (mem_rangeAdd_I_core A _).mp hy
      refine ⟨((ψ : H), A ψ), (hgraph _).mpr ⟨ψ, rfl⟩, ?_⟩
      rw [hT₂]
      have hy' : y = ⟨A ψ + Complex.I • (ψ : H), hVmem ψ⟩ := Subtype.ext hψ.symm
      rw [hy', hVapp ψ (hVmem ψ)]
  have hI₃ : T₃ '' (A.graph : Set (H × H)) = (V.graph : Set (H × H)) := by
    ext p
    rw [SetLike.mem_coe, LinearPMap.mem_graph_iff]
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨ψ, rfl⟩ := (hgraph g).mp hg
      rw [hT₃]
      exact ⟨⟨_, hVmem ψ⟩, rfl, hVapp ψ (hVmem ψ)⟩
    · rintro ⟨y, hy1, hy2⟩
      have hy : (y : H) ∈ rangeAdd A Complex.I := by rw [← hVdom]; exact y.2
      obtain ⟨ψ, hψ⟩ := (mem_rangeAdd_I_core A _).mp hy
      refine ⟨((ψ : H), A ψ), (hgraph _).mpr ⟨ψ, rfl⟩, ?_⟩
      rw [hT₃]
      have hy' : y = ⟨A ψ + Complex.I • (ψ : H), hVmem ψ⟩ := Subtype.ext hψ.symm
      rw [hy', hVapp ψ (hVmem ψ)] at hy2
      rw [hy'] at hy1
      exact Prod.ext hy1 hy2
  have e₁ := isClosed_iff_image_core A.graph T₁ hb₁
  have e₂ := isClosed_iff_image_core A.graph T₂ hb₂
  have e₃ := isClosed_iff_image_core A.graph T₃ hb₃
  rw [hI₁] at e₁
  rw [hI₂] at e₂
  rw [hI₃] at e₃
  tfae_have 1 ↔ 2 := e₁
  tfae_have 1 ↔ 3 := e₂
  tfae_have 1 ↔ 4 := e₃
  tfae_finish

#print axioms solution
