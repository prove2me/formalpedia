-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P28.lemma_1_17
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:15:03.056982+00:00
-- url     : https://prove2.me/submissions/597ac698-5006-4da2-8e8b-35b067ea7e51

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

/-- Lemma 1.17, PDF p.16: regularity into the projective limit is tested by
all its canonical limit maps. The limit has the induced product topology. -/
theorem solution
    (K : Type u) [Field K] [TopologicalSpace K] [T2Space K]
    [IsTopologicalDivisionRing K] (hK : ¬ DiscreteTopology K)
    (E : Type (max u v)) [AddCommGroup E] [Module K E] [TopologicalSpace E]
    [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul K E]
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)]
    (Fi : I → Type w) [∀ i, AddCommGroup (Fi i)] [∀ i, Module K (Fi i)]
    [∀ i, TopologicalSpace (Fi i)] [∀ i, T2Space (Fi i)]
    [∀ i, IsTopologicalAddGroup (Fi i)] [∀ i, ContinuousSMul K (Fi i)]
    (S : ProjectiveSystem K Fi)
    (U : Set E) (hU : IsOpen U) (f : U → projectiveLimit K Fi S)
    (k : WithTop ℕ) :
    bgnCr K (projectiveLimit K Fi S) k U f ↔
      ∀ i, bgnCr K (Fi i) k U (fun x => (f x).val i) := by
  constructor
  · intro h i n hn
    exact g66p_map ((ContinuousLinearMap.proj (R := K) (φ := Fi) i).comp
      (projectiveLimit K Fi S).subtypeL) n U f (h n hn)
  · intro h n hn
    have hp := g66p_pi Fi n U (fun x => (f x).val) (fun i => h i n hn)
    have hC : IsClosed ((projectiveLimit K Fi S : Submodule K (∀ i, Fi i)) : Set (∀ i, Fi i)) := by
      have : ((projectiveLimit K Fi S : Submodule K (∀ i, Fi i)) : Set (∀ i, Fi i)) =
          ⋂ i, ⋂ j, ⋂ (hij : i ≤ j), {x | S.bonding i j hij (x j) = x i} := by
        ext x; simp only [Set.mem_iInter, Set.mem_setOf_eq]; rfl
      rw [this]
      exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun hij =>
        isClosed_eq ((S.bonding i j hij).continuous.comp (continuous_apply j)) (continuous_apply i)
    have hcl := g66p_hcl_closed (K := K) _ (g66p_nebot hK) hC
    exact g66p_sub (projectiveLimit K Fi S) hcl n U hU (fun x => (f x).val) (fun x => (f x).2) hp

