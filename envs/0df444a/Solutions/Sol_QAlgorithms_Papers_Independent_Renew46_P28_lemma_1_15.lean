-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P28.lemma_1_15
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:12:48.164537+00:00
-- url     : https://prove2.me/submissions/5e22686e-29fd-4d92-9496-97f9e73d547b

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P28
open QAlgorithms.Papers.Independent.Renew46.P28

open Set

open scoped TensorProduct

universe u v w


open Set Filter Topology
universe w'

section G66P

variable {K : Type u} [Field K] [TopologicalSpace K]

theorem g66p_succ {F : Type w} [AddCommGroup F] [Module K F] [TopologicalSpace F] (n : ℕ)
    {E : Type (max u v)} [AddCommGroup E] [Module K E] [TopologicalSpace E] (U : Set E) (f : U → F) :
    bgnFinite K F (n + 1) U f ↔ Continuous f ∧ ∃ g : differenceDomain K U → F,
      Continuous g ∧ extendsDifferenceQuotient K U f g ∧ bgnFinite K F n (differenceDomain K U) g := by
  rw [bgnFinite]

theorem g66p_zero {F : Type w} [AddCommGroup F] [Module K F] [TopologicalSpace F]
    {E : Type (max u v)} [AddCommGroup E] [Module K E] [TopologicalSpace E] (U : Set E) (f : U → F) :
    bgnFinite K F 0 U f ↔ Continuous f := by
  rw [bgnFinite]

theorem g66p_map {F : Type w} [AddCommGroup F] [Module K F] [TopologicalSpace F]
    {G : Type w'} [AddCommGroup G] [Module K G] [TopologicalSpace G] (L : F →L[K] G) (n : ℕ) :
    ∀ {E : Type (max u v)} [AddCommGroup E] [Module K E] [TopologicalSpace E] (U : Set E) (f : U → F),
      bgnFinite K F n U f → bgnFinite K G n U (fun x => L (f x)) := by
  induction n with
  | zero =>
    intro E _ _ _ U f h
    rw [g66p_zero] at h ⊢
    exact L.continuous.comp h
  | succ n ih =>
    intro E _ _ _ U f h
    rw [g66p_succ] at h ⊢
    obtain ⟨hc, g, hg, hext, hn⟩ := h
    refine ⟨L.continuous.comp hc, fun z => L (g z), L.continuous.comp hg, ?_, ih _ g hn⟩
    intro z
    simp only [hext z, differenceQuotient, map_smul, map_sub]

theorem g66p_pi {I : Type*} (Fi : I → Type w) [∀ i, AddCommGroup (Fi i)] [∀ i, Module K (Fi i)]
    [∀ i, TopologicalSpace (Fi i)] (n : ℕ) :
    ∀ {E : Type (max u v)} [AddCommGroup E] [Module K E] [TopologicalSpace E] (U : Set E)
      (f : U → ∀ i, Fi i),
      (∀ i, bgnFinite K (Fi i) n U (fun x => f x i)) → bgnFinite K (∀ i, Fi i) n U f := by
  induction n with
  | zero =>
    intro E _ _ _ U f h
    rw [g66p_zero]
    exact continuous_pi fun i => (g66p_zero U _).1 (h i)
  | succ n ih =>
    intro E _ _ _ U f h
    rw [g66p_succ]
    have h' := fun i => (g66p_succ n U _).1 (h i)
    choose hc g hg hext hn using h'
    refine ⟨continuous_pi hc, fun z i => g i z, continuous_pi hg, ?_, ih _ _ hn⟩
    intro z
    funext i
    exact hext i z

variable [IsTopologicalRing K]

theorem g66p_open {E : Type v} [AddCommGroup E] [Module K E] [TopologicalSpace E]
    [ContinuousAdd E] [ContinuousSMul K E] {U : Set E} (hU : IsOpen U) :
    IsOpen (differenceDomain K U) := by
  have : differenceDomain K U =
      (fun w : E × E × K => (w.1, w.1 + w.2.2 • w.2.1)) ⁻¹' (U ×ˢ U) := by
    ext w; simp [differenceDomain]
  rw [this]
  exact (hU.prod hU).preimage (by fun_prop)

/-- Values of a continuous extended quotient lie in any set that is closed along punctured
scalar limits, once the punctured values do. -/
theorem g66p_core {F : Type w} [AddCommGroup F] [Module K F] [TopologicalSpace F] (C : Set F)
    (hcl : ∀ (φ : K → F) (a : F), Tendsto φ (𝓝[≠] (0 : K)) (𝓝 a) →
      (∀ᶠ s in 𝓝[≠] (0 : K), φ s ∈ C) → a ∈ C)
    {E : Type v} [AddCommGroup E] [Module K E] [TopologicalSpace E]
    [ContinuousAdd E] [ContinuousSMul K E] {U : Set E} (hU : IsOpen U)
    (g : differenceDomain K U → F) (hg : Continuous g)
    (hp : ∀ z : puncturedDifferenceDomain K U, g ⟨z.val, z.property.1⟩ ∈ C) :
    ∀ z, g z ∈ C := by
  rintro ⟨⟨x, y, t⟩, hz⟩
  by_cases ht : t = 0
  · subst ht
    have hD := g66p_open (K := K) hU
    classical
    let G : E × E × K → F := fun w => if h : w ∈ differenceDomain K U then g ⟨w, h⟩ else g ⟨_, hz⟩
    have hGon : ContinuousOn G (differenceDomain K U) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have : (differenceDomain K U).domRestrict G = g := by
        funext w; show G w.1 = g w; simp only [G, dif_pos w.2]
      rw [this]; exact hg
    have hGat : ContinuousAt G (x, y, 0) := hGon.continuousAt (hD.mem_nhds hz)
    have hι : Continuous fun s : K => (x, y, s) := by fun_prop
    have ht0 : Tendsto (fun s : K => G (x, y, s)) (𝓝 0) (𝓝 (G (x, y, 0))) :=
      hGat.tendsto.comp (hι.tendsto 0)
    have hG0 : G (x, y, 0) = g ⟨(x, y, 0), hz⟩ := by simp [G, hz]
    rw [hG0] at ht0
    refine hcl (fun s => G (x, y, s)) _ (ht0.mono_left nhdsWithin_le_nhds) ?_
    have hev : ∀ᶠ s in 𝓝 (0 : K), (x, y, s) ∈ differenceDomain K U :=
      (hι.tendsto 0) (hD.mem_nhds hz)
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with s hs hs0
    have := hp ⟨(x, y, s), hs, hs0⟩
    simpa [G, hs] using this
  · exact hp ⟨(x, y, t), hz, ht⟩

theorem g66p_sub {F : Type w} [AddCommGroup F] [Module K F] [TopologicalSpace F] (F0 : Submodule K F)
    (hcl : ∀ (φ : K → F) (a : F), Tendsto φ (𝓝[≠] (0 : K)) (𝓝 a) →
      (∀ᶠ s in 𝓝[≠] (0 : K), φ s ∈ F0) → a ∈ F0) (n : ℕ) :
    ∀ {E : Type (max u v)} [AddCommGroup E] [Module K E] [TopologicalSpace E]
      [ContinuousAdd E] [ContinuousSMul K E] (U : Set E) (hU : IsOpen U) (f : U → F)
      (hm : ∀ x, f x ∈ F0),
      bgnFinite K F n U f → bgnFinite K F0 n U (fun x => ⟨f x, hm x⟩) := by
  induction n with
  | zero =>
    intro E _ _ _ _ _ U hU f hm h
    rw [g66p_zero] at h ⊢
    exact h.subtype_mk _
  | succ n ih =>
    intro E _ _ _ _ _ U hU f hm h
    rw [g66p_succ] at h ⊢
    obtain ⟨hc, g, hg, hext, hn⟩ := h
    have gm : ∀ z, g z ∈ F0 := by
      refine g66p_core (F0 : Set F) hcl hU g hg ?_
      intro z
      rw [hext z]
      exact F0.smul_mem _ (F0.sub_mem (hm _) (hm _))
    refine ⟨hc.subtype_mk _, fun z => ⟨g z, gm z⟩, hg.subtype_mk _, ?_,
      ih _ (g66p_open hU) g gm hn⟩
    intro z
    apply Subtype.ext
    simp only [hext z, differenceQuotient, Submodule.coe_smul, Submodule.coe_sub]

theorem g66p_nebot [T2Space K] (hK : ¬ DiscreteTopology K) : (𝓝[≠] (0 : K)).NeBot := by
  rw [discreteTopology_iff_isOpen_singleton_zero, isOpen_singleton_iff_punctured_nhds] at hK
  exact ⟨hK⟩

end G66P

section G66Q
variable {K : Type u} [Field K] [TopologicalSpace K]

theorem g66p_hcl_closed {F : Type w} [TopologicalSpace F] (C : Set F) (hNe : (𝓝[≠] (0 : K)).NeBot)
    (hC : IsClosed C) : ∀ (φ : K → F) (a : F), Tendsto φ (𝓝[≠] (0 : K)) (𝓝 a) →
      (∀ᶠ s in 𝓝[≠] (0 : K), φ s ∈ C) → a ∈ C :=
  fun _ _ h1 h2 => hC.mem_of_tendsto h1 h2

theorem g66p_hcl_seq {F : Type w} [TopologicalSpace F] (C : Set F) (hNe : (𝓝[≠] (0 : K)).NeBot)
    (hM : TopologicalSpace.MetrizableSpace K)
    (hC : IsSeqClosed C) : ∀ (φ : K → F) (a : F), Tendsto φ (𝓝[≠] (0 : K)) (𝓝 a) →
      (∀ᶠ s in 𝓝[≠] (0 : K), φ s ∈ C) → a ∈ C := by
  intro φ a h1 h2
  obtain ⟨x, hx⟩ := Filter.exists_seq_tendsto (𝓝[≠] (0 : K))
  have h3 := h1.comp hx
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hx.eventually h2)
  refine hC (x := fun n => φ (x (n + N))) (fun n => hN _ (Nat.le_add_left _ _)) ?_
  exact (tendsto_add_atTop_iff_nat N).2 h3

end G66Q

/-- Lemma 1.15, PDF p.16: corestriction to a closed subspace, or to a
sequentially closed subspace when the scalar field is metrizable. The subspace
carries precisely the induced topology. -/
theorem solution
    (K : Type u) [Field K] [TopologicalSpace K] [T2Space K]
    [IsTopologicalDivisionRing K] (hK : ¬ DiscreteTopology K)
    (E : Type (max u v)) [AddCommGroup E] [Module K E] [TopologicalSpace E]
    [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul K E]
    (F : Type w) [AddCommGroup F] [Module K F] [TopologicalSpace F]
    [T2Space F] [IsTopologicalAddGroup F] [ContinuousSMul K F]
    (U : Set E) (hU : IsOpen U) (f : U → F) (k : WithTop ℕ)
    (hf : bgnCr K F k U f) (F0 : Submodule K F)
    (himage : ∀ x, f x ∈ F0)
    (hclosed : IsClosed (F0 : Set F) ∨
      (IsSeqClosed (F0 : Set F) ∧ TopologicalSpace.MetrizableSpace K)) :
    bgnCr K F0 k U (fun x => ⟨f x, himage x⟩) := by
  have hNe := g66p_nebot hK
  have hcl : ∀ (φ : K → F) (a : F), Tendsto φ (𝓝[≠] (0 : K)) (𝓝 a) →
      (∀ᶠ s in 𝓝[≠] (0 : K), φ s ∈ F0) → a ∈ F0 := by
    rcases hclosed with h | ⟨h, hM⟩
    · exact g66p_hcl_closed _ hNe h
    · exact g66p_hcl_seq _ hNe hM h
  intro n hn
  exact g66p_sub F0 hcl n U hU f himage (hf n hn)

