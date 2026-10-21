-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P28.lemma_1_12
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:43:40.430996+00:00
-- url     : https://prove2.me/submissions/28ad6ca8-5bab-40f4-940d-481b83d8cd54

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P28
open QAlgorithms.Papers.Independent.Renew46.P28

open Set

open scoped TensorProduct

universe u v w


open Set Filter Topology
universe v1 v2 g

section G66K

variable {K : Type u} [Field K] [TopologicalSpace K]

theorem g66k_succ {F : Type w} [AddCommGroup F] [Module K F] [TopologicalSpace F] (n : ℕ)
    {E : Type (max u v)} [AddCommGroup E] [Module K E] [TopologicalSpace E] (U : Set E) (f : U → F) :
    bgnFinite K F (n + 1) U f ↔ Continuous f ∧ ∃ g : differenceDomain K U → F,
      Continuous g ∧ extendsDifferenceQuotient K U f g ∧ bgnFinite K F n (differenceDomain K U) g := by
  rw [bgnFinite]

theorem g66k_zero {F : Type w} [AddCommGroup F] [Module K F] [TopologicalSpace F]
    {E : Type (max u v)} [AddCommGroup E] [Module K E] [TopologicalSpace E] (U : Set E) (f : U → F) :
    bgnFinite K F 0 U f ↔ Continuous f := by
  rw [bgnFinite]

theorem g66k_cont {F : Type w} [AddCommGroup F] [Module K F] [TopologicalSpace F] (n : ℕ)
    {E : Type (max u v)} [AddCommGroup E] [Module K E] [TopologicalSpace E] (U : Set E) (f : U → F)
    (h : bgnFinite K F n U f) : Continuous f := by
  cases n with
  | zero => exact (g66k_zero U f).1 h
  | succ n => exact ((g66k_succ n U f).1 h).1

theorem g66k_mono {F : Type w} [AddCommGroup F] [Module K F] [TopologicalSpace F] (n : ℕ) :
    ∀ {E : Type (max u v)} [AddCommGroup E] [Module K E] [TopologicalSpace E] (U : Set E) (f : U → F),
      bgnFinite K F (n + 1) U f → bgnFinite K F n U f := by
  induction n with
  | zero =>
    intro E _ _ _ U f h
    exact (g66k_zero U f).2 ((g66k_succ 0 U f).1 h).1
  | succ n ih =>
    intro E _ _ _ U f h
    obtain ⟨hc, g, hg, hext, hn⟩ := (g66k_succ _ U f).1 h
    exact (g66k_succ n U f).2 ⟨hc, g, hg, hext, ih _ g hn⟩

/-- A continuous linear map, restricted to any domain, is C^n. -/
theorem g66k_clm {G : Type w} [AddCommGroup G] [Module K G] [TopologicalSpace G] (n : ℕ) :
    ∀ {E : Type (max u v)} [AddCommGroup E] [Module K E] [TopologicalSpace E] (L : E →L[K] G)
      (V : Set E), bgnFinite K G n V (fun x => L x.val) := by
  induction n with
  | zero =>
    intro E _ _ _ L V
    exact (g66k_zero V _).2 (L.continuous.comp continuous_subtype_val)
  | succ n ih =>
    intro E _ _ _ L V
    refine (g66k_succ n V _).2 ⟨L.continuous.comp continuous_subtype_val,
      fun z => L z.val.2.1, L.continuous.comp (continuous_fst.comp (continuous_snd.comp continuous_subtype_val)), ?_,
      ih (L.comp ((ContinuousLinearMap.fst K E K).comp (ContinuousLinearMap.snd K E (E × K)))) _⟩
    intro z
    have ht : z.val.2.2 ≠ 0 := z.property.2
    simp only [differenceQuotient, map_add, map_smul, add_sub_cancel_left, inv_smul_smul₀ ht]

theorem g66k_pair {F : Type w} [AddCommGroup F] [Module K F] [TopologicalSpace F]
    {G : Type g} [AddCommGroup G] [Module K G] [TopologicalSpace G] (n : ℕ) :
    ∀ {E : Type (max u v)} [AddCommGroup E] [Module K E] [TopologicalSpace E] (U : Set E)
      (f : U → F) (h : U → G),
      bgnFinite K F n U f → bgnFinite K G n U h → bgnFinite K (F × G) n U (fun x => (f x, h x)) := by
  induction n with
  | zero =>
    intro E _ _ _ U f h hf hh
    exact (g66k_zero U _).2 (((g66k_zero U f).1 hf).prodMk ((g66k_zero U h).1 hh))
  | succ n ih =>
    intro E _ _ _ U f h hf hh
    obtain ⟨hc, g1, hg1, hext1, hn1⟩ := (g66k_succ _ U f).1 hf
    obtain ⟨hc', g2, hg2, hext2, hn2⟩ := (g66k_succ _ U h).1 hh
    refine (g66k_succ n U _).2 ⟨hc.prodMk hc', fun z => (g1 z, g2 z), hg1.prodMk hg2, ?_, ih _ _ _ hn1 hn2⟩
    intro z
    show (g1 _, g2 _) = _
    rw [hext1 z, hext2 z]
    simp [differenceQuotient]

end G66K

section G66K2

variable {K : Type u} [Field K] [TopologicalSpace K]

/-- Precomposition with a continuous linear map. -/
theorem g66k_precomp {F : Type w} [AddCommGroup F] [Module K F] [TopologicalSpace F] (n : ℕ) :
    ∀ {E : Type (max u v1)} [AddCommGroup E] [Module K E] [TopologicalSpace E]
      {E' : Type (max u v2)} [AddCommGroup E'] [Module K E'] [TopologicalSpace E']
      (U : Set E) (V : Set E') (f : U → F) (L : E' →L[K] E) (hL : ∀ x : V, L x.val ∈ U),
      bgnFinite K F n U f → bgnFinite K F n V (fun x => f ⟨L x.val, hL x⟩) := by
  induction n with
  | zero =>
    intro E _ _ _ E' _ _ _ U V f L hL hf
    rw [g66k_zero] at hf ⊢
    exact hf.comp ((L.continuous.comp continuous_subtype_val).subtype_mk _)
  | succ n ih =>
    intro E _ _ _ E' _ _ _ U V f L hL hf
    rw [g66k_succ] at hf
    obtain ⟨hc, f1, hf1, hext, hn⟩ := hf
    have hmem : ∀ z : differenceDomain K V, (L z.val.1, L z.val.2.1, z.val.2.2) ∈ differenceDomain K U := by
      intro z
      refine ⟨hL ⟨_, z.property.1⟩, ?_⟩
      have := hL ⟨_, z.property.2⟩
      simpa [map_add, map_smul] using this
    let M : (E' × E' × K) →L[K] (E × E × K) := L.prodMap (L.prodMap (ContinuousLinearMap.id K K))
    rw [g66k_succ]
    refine ⟨hc.comp ((L.continuous.comp continuous_subtype_val).subtype_mk _),
      fun z => f1 ⟨M z.val, hmem z⟩, hf1.comp ((M.continuous.comp continuous_subtype_val).subtype_mk _),
      ?_, ih _ _ f1 M hmem hn⟩
    intro z
    have ht : z.val.2.2 ≠ 0 := z.property.2
    have := hext ⟨M z.val, hmem ⟨z.val, z.property.1⟩, ht⟩
    simp only at this ⊢
    rw [this]
    simp only [differenceQuotient, M, ContinuousLinearMap.coe_prodMap', Prod.map,
      ContinuousLinearMap.coe_id', id]
    congr 3
    simp [map_add, map_smul]

end G66K2

section G66K3

variable {K : Type u} [Field K] [TopologicalSpace K]

theorem g66k_id_step {E : Type (max u v2)} [AddCommGroup E] [Module K E]
    {G : Type w} [AddCommGroup G] [Module K G]
    (V : Set E) (g : V → G) (g1 : differenceDomain K V → G)
    (hextg : extendsDifferenceQuotient K V g g1) (z : differenceDomain K V) :
    g ⟨z.val.1 + z.val.2.2 • z.val.2.1, z.2.2⟩ = g ⟨z.val.1, z.2.1⟩ + z.val.2.2 • g1 z := by
  by_cases ht : z.val.2.2 = 0
  · have e : (⟨z.val.1 + z.val.2.2 • z.val.2.1, z.2.2⟩ : V) = ⟨z.val.1, z.2.1⟩ :=
      Subtype.ext (by simp [ht])
    rw [e]
    simp [ht]
  · have := hextg ⟨z.val, z.2, ht⟩
    simp only [differenceQuotient] at this
    rw [this, smul_inv_smul₀ ht]
    abel

/-- Chain rule. -/
theorem g66k_chain {F : Type w} [AddCommGroup F] [Module K F] [TopologicalSpace F] (n : ℕ) :
    ∀ {E : Type (max u v1)} [AddCommGroup E] [Module K E] [TopologicalSpace E]
      {E' : Type (max u v2)} [AddCommGroup E'] [Module K E'] [TopologicalSpace E']
      (U : Set E) (V : Set E') (f : U → F) (g : V → E) (hg : ∀ x, g x ∈ U),
      bgnFinite K F n U f → bgnFinite K E n V g → bgnFinite K F n V (fun x => f ⟨g x, hg x⟩) := by
  induction n with
  | zero =>
    intro E _ _ _ E' _ _ _ U V f g hg hf hgc
    rw [g66k_zero] at hf hgc ⊢
    exact hf.comp (hgc.subtype_mk _)
  | succ n ih =>
    intro E _ _ _ E' _ _ _ U V f g hg hf hgc
    have hgn := g66k_mono n V g hgc
    rw [g66k_succ] at hf hgc
    obtain ⟨hcf, f1, hf1, hextf, hnf⟩ := hf
    obtain ⟨hcg, g1, hg1, hextg, hng⟩ := hgc
    have hid := g66k_id_step V g g1 hextg
    let Γ : differenceDomain K V → E × E × K := fun z => (g ⟨z.val.1, z.2.1⟩, g1 z, z.val.2.2)
    have hΓ : ∀ z, Γ z ∈ differenceDomain K U := fun z => ⟨hg _, by
      show g ⟨z.val.1, z.2.1⟩ + z.val.2.2 • g1 z ∈ U
      rw [← hid z]; exact hg _⟩
    have hp1 : bgnFinite K E n (differenceDomain K V) (fun z => g ⟨z.val.1, z.2.1⟩) :=
      g66k_precomp n V (differenceDomain K V) g (ContinuousLinearMap.fst K E' (E' × K))
        (fun x => x.2.1) hgn
    have hp3 : bgnFinite K K n (differenceDomain K V) (fun z => z.val.2.2) :=
      g66k_clm n ((ContinuousLinearMap.snd K E' K).comp (ContinuousLinearMap.snd K E' (E' × K))) _
    have hΓn : bgnFinite K (E × E × K) n (differenceDomain K V) Γ :=
      g66k_pair n _ _ _ hp1 (g66k_pair n _ _ _ hng hp3)
    have hcΓ : Continuous Γ := (g66k_cont n _ _ hΓn)
    rw [g66k_succ]
    refine ⟨hcf.comp (hcg.subtype_mk _), fun z => f1 ⟨Γ z, hΓ z⟩, hf1.comp (hcΓ.subtype_mk _), ?_,
      ih (differenceDomain K U) (differenceDomain K V) f1 Γ hΓ hnf hΓn⟩
    intro z
    have ht : z.val.2.2 ≠ 0 := z.property.2
    have := hextf ⟨Γ ⟨z.val, z.property.1⟩, hΓ _, ht⟩
    simp only at this ⊢
    rw [this]
    simp only [differenceQuotient, Γ]
    congr 2
    apply congrArg f
    apply Subtype.ext
    exact (hid ⟨z.val, z.property.1⟩).symm

end G66K3

section G66K4

variable {K : Type u} [Field K] [TopologicalSpace K]

theorem g66k_map {F : Type w} [AddCommGroup F] [Module K F] [TopologicalSpace F]
    {G : Type g} [AddCommGroup G] [Module K G] [TopologicalSpace G] (L : F →L[K] G) (n : ℕ) :
    ∀ {E : Type (max u v)} [AddCommGroup E] [Module K E] [TopologicalSpace E] (U : Set E) (f : U → F),
      bgnFinite K F n U f → bgnFinite K G n U (fun x => L (f x)) := by
  induction n with
  | zero =>
    intro E _ _ _ U f h
    rw [g66k_zero] at h ⊢
    exact L.continuous.comp h
  | succ n ih =>
    intro E _ _ _ U f h
    rw [g66k_succ] at h ⊢
    obtain ⟨hc, g, hg, hext, hn⟩ := h
    refine ⟨L.continuous.comp hc, fun z => L (g z), L.continuous.comp hg, ?_, ih _ g hn⟩
    intro z
    simp only [hext z, differenceQuotient, map_smul, map_sub]

theorem g66k_add {F : Type w} [AddCommGroup F] [Module K F] [TopologicalSpace F] [ContinuousAdd F]
    (n : ℕ) {E : Type (max u v)} [AddCommGroup E] [Module K E] [TopologicalSpace E] (U : Set E)
    (f h : U → F) (hf : bgnFinite K F n U f) (hh : bgnFinite K F n U h) :
    bgnFinite K F n U (fun x => f x + h x) :=
  g66k_map (ContinuousLinearMap.fst K F F + ContinuousLinearMap.snd K F F) n U _
    (g66k_pair n U f h hf hh)

theorem g66k_sub {F : Type w} [AddCommGroup F] [Module K F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    (n : ℕ) {E : Type (max u v)} [AddCommGroup E] [Module K E] [TopologicalSpace E] (U : Set E)
    (f h : U → F) (hf : bgnFinite K F n U f) (hh : bgnFinite K F n U h) :
    bgnFinite K F n U (fun x => f x - h x) :=
  g66k_map (ContinuousLinearMap.fst K F F - ContinuousLinearMap.snd K F F) n U _
    (g66k_pair n U f h hf hh)

variable [IsTopologicalRing K]

/-- Scalar multiplication K × G → G is C^n on every domain. -/
theorem g66k_smul (n : ℕ) :
    ∀ {G : Type g} [AddCommGroup G] [Module K G] [TopologicalSpace G] [ContinuousAdd G]
      [ContinuousSMul K G] (W : Set (K × G)), bgnFinite K G n W (fun z => z.val.1 • z.val.2) := by
  induction n with
  | zero =>
    intro G _ _ _ _ _ W
    rw [g66k_zero]
    exact continuous_smul.comp continuous_subtype_val
  | succ n ih =>
    intro G _ _ _ _ _ W
    let L1 : (K × G) × (K × G) × K →L[K] K × G :=
      ((ContinuousLinearMap.fst K K G).comp ((ContinuousLinearMap.fst K (K × G) K).comp
        (ContinuousLinearMap.snd K (K × G) ((K × G) × K)))).prod
      ((ContinuousLinearMap.snd K K G).comp (ContinuousLinearMap.fst K (K × G) ((K × G) × K)))
    let L2 : (K × G) × (K × G) × K →L[K] K × G :=
      ((ContinuousLinearMap.fst K K G).comp (ContinuousLinearMap.fst K (K × G) ((K × G) × K))).prod
      ((ContinuousLinearMap.snd K K G).comp ((ContinuousLinearMap.fst K (K × G) K).comp
        (ContinuousLinearMap.snd K (K × G) ((K × G) × K))))
    let L3 : (K × G) × (K × G) × K →L[K] K × G :=
      (ContinuousLinearMap.fst K (K × G) K).comp (ContinuousLinearMap.snd K (K × G) ((K × G) × K))
    have hS := ih (Set.univ : Set (K × G))
    have h1 : bgnFinite K G n (differenceDomain K W) (fun z => (L1 z.val).1 • (L1 z.val).2) :=
      g66k_precomp n Set.univ (differenceDomain K W) _ L1 (fun _ => trivial) hS
    have h2 : bgnFinite K G n (differenceDomain K W) (fun z => (L2 z.val).1 • (L2 z.val).2) :=
      g66k_precomp n Set.univ (differenceDomain K W) _ L2 (fun _ => trivial) hS
    have h3i : bgnFinite K G n (differenceDomain K W) (fun z => (L3 z.val).1 • (L3 z.val).2) :=
      g66k_precomp n Set.univ (differenceDomain K W) _ L3 (fun _ => trivial) hS
    have hs : bgnFinite K K n (differenceDomain K W) (fun z => z.val.2.2) :=
      g66k_clm n ((ContinuousLinearMap.snd K (K × G) K).comp
        (ContinuousLinearMap.snd K (K × G) ((K × G) × K))) _
    have h3 := g66k_chain n (Set.univ : Set (K × G)) (differenceDomain K W) _
      (fun z => (z.val.2.2, (L3 z.val).1 • (L3 z.val).2)) (fun _ => trivial) hS
      (g66k_pair n _ _ _ hs h3i)
    have hsum := g66k_add n _ _ _ (g66k_add n _ _ _ h1 h2) h3
    rw [g66k_succ]
    refine ⟨continuous_smul.comp continuous_subtype_val, _, g66k_cont n _ _ hsum, ?_, hsum⟩
    intro z
    have hz : z.val.2.2 ≠ 0 := z.property.2
    obtain ⟨⟨⟨t, w⟩, ⟨t', w'⟩, s⟩, hzm⟩ := z
    simp only [differenceQuotient, L1, L2, L3, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hz ⊢
    symm
    rw [inv_smul_eq_iff₀ hz]
    module

end G66K4

section G66K5

variable {K : Type u} [Field K] [TopologicalSpace K] [IsTopologicalRing K]

theorem g66k_smulF {G : Type g} [AddCommGroup G] [Module K G] [TopologicalSpace G] [ContinuousAdd G]
    [ContinuousSMul K G] (n : ℕ) {E : Type (max u v)} [AddCommGroup E] [Module K E] [TopologicalSpace E]
    (W : Set E) (p : W → K) (r : W → G) (hp : bgnFinite K K n W p) (hr : bgnFinite K G n W r) :
    bgnFinite K G n W (fun z => p z • r z) :=
  g66k_chain n (Set.univ : Set (K × G)) W (fun z => z.val.1 • z.val.2) (fun z => (p z, r z))
    (fun _ => trivial) (g66k_smul n _) (g66k_pair n W p r hp hr)

theorem g66k_mul (n : ℕ) {E : Type (max u v)} [AddCommGroup E] [Module K E] [TopologicalSpace E]
    (W : Set E) (p r : W → K) (hp : bgnFinite K K n W p) (hr : bgnFinite K K n W r) :
    bgnFinite K K n W (fun z => p z * r z) :=
  g66k_smulF n W p r hp hr

end G66K5

section G66K6

variable {K : Type u} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]

theorem g66k_inv (n : ℕ) :
    ∀ {E : Type (max u v)} [AddCommGroup E] [Module K E] [TopologicalSpace E]
      (W : Set E) (a : W → K) (ha : ∀ z, a z ≠ 0),
      bgnFinite K K n W a → bgnFinite K K n W (fun z => (a z)⁻¹) := by
  induction n with
  | zero =>
    intro E _ _ _ W a ha h
    rw [g66k_zero] at h ⊢
    exact h.inv₀ ha
  | succ n ih =>
    intro E _ _ _ W a ha h
    have han := g66k_mono n W a h
    rw [g66k_succ] at h
    obtain ⟨hc, a1, ha1, hext, hn⟩ := h
    have hid := g66k_id_step W a a1 hext
    let a0 : differenceDomain K W → K := fun z => a ⟨z.val.1, z.2.1⟩
    let b : differenceDomain K W → K := fun z => a ⟨z.val.1 + z.val.2.2 • z.val.2.1, z.2.2⟩
    have ha0 : bgnFinite K K n (differenceDomain K W) a0 :=
      g66k_precomp n W (differenceDomain K W) a (ContinuousLinearMap.fst K E (E × K)) (fun x => x.2.1) han
    have hs : bgnFinite K K n (differenceDomain K W) (fun z => z.val.2.2) :=
      g66k_clm n ((ContinuousLinearMap.snd K E K).comp (ContinuousLinearMap.snd K E (E × K))) _
    have hb : bgnFinite K K n (differenceDomain K W) b := by
      have e : b = fun z => a0 z + z.val.2.2 • a1 z := funext hid
      rw [e]
      exact g66k_add n _ _ _ ha0 (g66k_smulF n _ _ _ hs hn)
    have hia0 := ih _ a0 (fun z => ha _) ha0
    have hib := ih _ b (fun z => ha _) hb
    have hfin := g66k_map (-ContinuousLinearMap.id K K) n _ _ (g66k_mul n _ _ _ hn (g66k_mul n _ _ _ hia0 hib))
    rw [g66k_succ]
    refine ⟨hc.inv₀ ha, _, g66k_cont n _ _ hfin, ?_, hfin⟩
    intro z
    have ht : z.val.2.2 ≠ 0 := z.property.2
    have h1 := hext z
    have hz0 : a0 ⟨z.val, z.property.1⟩ ≠ 0 := ha _
    have hz1 : b ⟨z.val, z.property.1⟩ ≠ 0 := ha _
    simp only [differenceQuotient, smul_eq_mul] at h1 ⊢
    simp only [a0, b] at hz0 hz1 ⊢
    rw [h1]
    simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply]
    field_simp
    ring

end G66K6

theorem g66k_open {K : Type u} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    {E : Type v} [AddCommGroup E] [Module K E] [TopologicalSpace E]
    [ContinuousAdd E] [ContinuousSMul K E] {U : Set E} (hU : IsOpen U) :
    IsOpen (differenceDomain K U) := by
  have : differenceDomain K U =
      (fun w : E × E × K => (w.1, w.1 + w.2.2 • w.2.1)) ⁻¹' (U ×ˢ U) := by
    ext w; simp [differenceDomain]
  rw [this]
  exact (hU.prod hU).preimage (by fun_prop)

theorem g66k_nebot {K : Type u} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    (hK : ¬ DiscreteTopology K) : (𝓝[≠] (0 : K)).NeBot := by
  rw [discreteTopology_iff_isOpen_singleton_zero, isOpen_singleton_iff_punctured_nhds] at hK
  exact ⟨hK⟩

section G66L

theorem g66l_glue {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (S : Set X)
    (h : S → Y) (H : ∀ x : S, ∃ O : Set X, IsOpen O ∧ x.val ∈ O ∧ ∃ hO : O ⊆ S, ∃ h' : O → Y,
      Continuous h' ∧ ∀ y : O, h ⟨y.val, hO y.2⟩ = h' y) : Continuous h := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨O, hO, hxO, hOS, h', hc, heq⟩ := H x
  have hon : ContinuousOn h {y : S | y.val ∈ O} := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : {y : S | y.val ∈ O}.domRestrict h = fun y => h' ⟨y.val.val, y.property⟩ := by
      funext y
      exact heq ⟨y.val.val, y.property⟩
    rw [this]
    exact hc.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
  exact hon.continuousAt ((hO.preimage continuous_subtype_val).mem_nhds hxO)

variable {K : Type u} [Field K] [TopologicalSpace K]

open Classical in
theorem g66l_lim {E : Type v} [TopologicalSpace E] {F : Type w} [TopologicalSpace F]
    (D : Set (E × E × K)) (hD : IsOpen D) (g : D → F) (hg : Continuous g) (z : E × E × K) (hz : z ∈ D) :
    Tendsto (fun s : K => if h : (z.1, z.2.1, s) ∈ D then g ⟨_, h⟩ else g ⟨z, hz⟩) (𝓝 z.2.2)
      (𝓝 (g ⟨z, hz⟩)) := by
  classical
  let G : E × E × K → F := fun w => if h : w ∈ D then g ⟨w, h⟩ else g ⟨z, hz⟩
  have hGon : ContinuousOn G D := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : D.domRestrict G = g := by
      funext w; show G w.1 = g w; simp only [G, dif_pos w.2]
    rw [this]; exact hg
  have hGat : ContinuousAt G z := hGon.continuousAt (hD.mem_nhds hz)
  have hι : Continuous fun s : K => (z.1, z.2.1, s) := by fun_prop
  have h1 := hGat.tendsto.comp (hι.tendsto z.2.2)
  have hG0 : G z = g ⟨z, hz⟩ := by simp [G, hz]
  rw [hG0] at h1
  exact h1

theorem g66l_agree [IsTopologicalRing K] (hNe : (𝓝[≠] (0 : K)).NeBot)
    {E : Type v} [TopologicalSpace E] {F : Type w} [TopologicalSpace F] [T2Space F]
    (D1 D2 : Set (E × E × K)) (h1 : IsOpen D1) (h2 : IsOpen D2) (g1 : D1 → F) (g2 : D2 → F)
    (hg1 : Continuous g1) (hg2 : Continuous g2)
    (hpt : ∀ w (hw1 : w ∈ D1) (hw2 : w ∈ D2), w.2.2 ≠ 0 → g1 ⟨w, hw1⟩ = g2 ⟨w, hw2⟩)
    (z : E × E × K) (hz1 : z ∈ D1) (hz2 : z ∈ D2) (hz0 : z.2.2 = 0) :
    g1 ⟨z, hz1⟩ = g2 ⟨z, hz2⟩ := by
  classical
  have t1 := (g66l_lim D1 h1 g1 hg1 z hz1).mono_left (nhdsWithin_le_nhds (s := {z.2.2}ᶜ))
  have t2 := (g66l_lim D2 h2 g2 hg2 z hz2).mono_left (nhdsWithin_le_nhds (s := {z.2.2}ᶜ))
  rw [hz0] at t1 t2
  have hι : Continuous fun s : K => (z.1, z.2.1, s) := by fun_prop
  have e1 : ∀ᶠ s in 𝓝 (0 : K), (z.1, z.2.1, s) ∈ D1 := by
    have := (hι.tendsto 0) (h1.mem_nhds (show (z.1, z.2.1, (0 : K)) ∈ D1 by rw [← hz0]; exact hz1))
    exact this
  have e2 : ∀ᶠ s in 𝓝 (0 : K), (z.1, z.2.1, s) ∈ D2 := by
    have := (hι.tendsto 0) (h2.mem_nhds (show (z.1, z.2.1, (0 : K)) ∈ D2 by rw [← hz0]; exact hz2))
    exact this
  refine tendsto_nhds_unique t1 (t2.congr' ?_)
  filter_upwards [nhdsWithin_le_nhds e1, nhdsWithin_le_nhds e2, self_mem_nhdsWithin] with s hs1 hs2 hs0
  simp only [dif_pos hs1, dif_pos hs2]
  exact (hpt _ hs1 hs2 hs0).symm

end G66L

section G66L2

variable {K : Type u} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]

theorem g66l_quot {E : Type (max u v)} [AddCommGroup E] [Module K E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul K E]
    {F : Type w} [AddCommGroup F] [Module K F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul K F] (n : ℕ) (U : Set E) (f : U → F)
    (hf : bgnFinite K F n U f) :
    bgnFinite K F n (puncturedDifferenceDomain K U) (differenceQuotient K U f) := by
  let P := puncturedDifferenceDomain K U
  have hs : bgnFinite K K n P (fun z => z.val.2.2) :=
    g66k_clm n ((ContinuousLinearMap.snd K E K).comp (ContinuousLinearMap.snd K E (E × K))) _
  have hy : bgnFinite K E n P (fun z => z.val.2.1) :=
    g66k_clm n ((ContinuousLinearMap.fst K E K).comp (ContinuousLinearMap.snd K E (E × K))) _
  have hx : bgnFinite K E n P (fun z => z.val.1) :=
    g66k_clm n (ContinuousLinearMap.fst K E (E × K)) _
  have hinv : bgnFinite K K n P (fun z => (z.val.2.2)⁻¹) :=
    g66k_inv n P (fun z => z.val.2.2) (fun z => z.property.2) hs
  have hφ : bgnFinite K E n P (fun z => z.val.1 + z.val.2.2 • z.val.2.1) :=
    g66k_add n P _ _ hx (g66k_smulF n P _ _ hs hy)
  have hfφ := g66k_chain n U P f (fun z => z.val.1 + z.val.2.2 • z.val.2.1)
    (fun z => z.property.1.2) hf hφ
  have hfπ : bgnFinite K F n P (fun z => f ⟨z.val.1, z.property.1.1⟩) :=
    g66k_precomp n U P f (ContinuousLinearMap.fst K E (E × K)) (fun z => z.property.1.1) hf
  exact g66k_smulF n P _ _ hinv (g66k_sub n P _ _ hfφ hfπ)

theorem g66l_popen {E : Type v} [AddCommGroup E] [Module K E] [TopologicalSpace E]
    [ContinuousAdd E] [ContinuousSMul K E] [T2Space K] {U : Set E} (hU : IsOpen U) :
    IsOpen (puncturedDifferenceDomain K U) := by
  have : puncturedDifferenceDomain K U = differenceDomain K U ∩ {z | z.2.2 ≠ 0} := by
    ext z; simp [puncturedDifferenceDomain]
  rw [this]
  exact (g66k_open hU).inter (isOpen_compl_singleton.preimage (continuous_snd.comp continuous_snd))

universe ι

theorem g66l_loc [T2Space K] (hNe : (𝓝[≠] (0 : K)).NeBot)
    {F : Type w} [AddCommGroup F] [Module K F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul K F] [T2Space F] (n : ℕ) :
    ∀ {E : Type (max u v)} [AddCommGroup E] [Module K E] [TopologicalSpace E]
      [IsTopologicalAddGroup E] [ContinuousSMul K E]
      (U : Set E) (hU : IsOpen U) (f : U → F) {I : Type ι} (Ui : I → Set E)
      (hUi : ∀ i, IsOpen (Ui i)) (hsub : ∀ i, Ui i ⊆ U) (hcover : U = ⋃ i, Ui i)
      (hloc : ∀ i, bgnFinite K F n (Ui i) (fun x => f ⟨x.val, hsub i x.property⟩)),
      bgnFinite K F n U f := by
  induction n with
  | zero =>
    intro E _ _ _ _ _ U hU f I Ui hUi hsub hcover hloc
    rw [g66k_zero]
    apply g66l_glue U f
    intro x
    have hx : x.val ∈ ⋃ i, Ui i := hcover ▸ x.property
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    exact ⟨Ui i, hUi i, hi, hsub i, _, (g66k_zero _ _).1 (hloc i), fun y => rfl⟩
  | succ n ih =>
    intro E _ _ _ _ _ U hU f I Ui hUi hsub hcover hloc
    classical
    have hfn : bgnFinite K F n U f :=
      ih U hU f Ui hUi hsub hcover (fun i => g66k_mono n _ _ (hloc i))
    have hloc' := fun i => (g66k_succ n _ _).1 (hloc i)
    choose hci gi hgi hexti hni using hloc'
    have hx : ∀ z : differenceDomain K U, ∃ i, z.val.1 ∈ Ui i := by
      intro z
      have : z.val.1 ∈ ⋃ i, Ui i := hcover ▸ z.property.1
      exact mem_iUnion.1 this
    choose idx hidx using hx
    have memD : ∀ i (z : E × E × K), z.1 ∈ Ui i → z.2.2 = 0 → z ∈ differenceDomain K (Ui i) := by
      intro i z h h0
      exact ⟨h, by simp [h0, h]⟩
    have hDsub : ∀ i, differenceDomain K (Ui i) ⊆ differenceDomain K U :=
      fun i w hw => ⟨hsub i hw.1, hsub i hw.2⟩
    let g : differenceDomain K U → F := fun z =>
      if ht : z.val.2.2 = 0 then gi (idx z) ⟨z.val, memD _ z.val (hidx z) ht⟩
      else differenceQuotient K U f ⟨z.val, z.property, ht⟩
    have hq : ∀ i (w : E × E × K) (hw : w ∈ differenceDomain K (Ui i)) (h0 : w.2.2 ≠ 0),
        gi i ⟨w, hw⟩ = differenceQuotient K U f ⟨w, hDsub i hw, h0⟩ := by
      intro i w hw h0
      rw [hexti i ⟨w, hw, h0⟩]
      rfl
    have hDo : ∀ i, IsOpen (differenceDomain K (Ui i)) := fun i => g66k_open (hUi i)
    have hA : ∀ i (w : differenceDomain K (Ui i)), g ⟨w.val, hDsub i w.property⟩ = gi i w := by
      intro i w
      by_cases ht : w.val.2.2 = 0
      · simp only [g, dif_pos ht]
        refine g66l_agree hNe _ _ (hDo _) (hDo i) (gi _) (gi i) (hgi _) (hgi i) ?_ _ _ _ ht
        intro w' h1 h2 h0
        rw [hq _ w' h1 h0, hq _ w' h2 h0]
      · simp only [g, dif_neg ht]
        exact (hq i w.val w.property ht).symm
    have hP : IsOpen (puncturedDifferenceDomain K U) := g66l_popen hU
    have hqn := g66l_quot n U f hfn
    have hgc : Continuous g := by
      apply g66l_glue _ g
      intro z
      by_cases ht : z.val.2.2 = 0
      · exact ⟨_, hDo (idx z), memD _ z.val (hidx z) ht, hDsub _, gi (idx z), hgi _, hA _⟩
      · refine ⟨_, hP, ⟨z.property, ht⟩, fun w hw => hw.1, differenceQuotient K U f,
          g66k_cont n _ _ hqn, fun y => ?_⟩
        simp only [g, dif_neg y.property.2]
    let piece : Option I → Set (E × E × K) := fun o => match o with
      | none => puncturedDifferenceDomain K U
      | some i => differenceDomain K (Ui i)
    have hpsub : ∀ o, piece o ⊆ differenceDomain K U := by
      intro o; cases o with
      | none => exact fun w hw => hw.1
      | some i => exact hDsub i
    have hpopen : ∀ o, IsOpen (piece o) := by
      intro o; cases o with
      | none => exact hP
      | some i => exact hDo i
    have hpcover : differenceDomain K U = ⋃ o, piece o := by
      ext w
      constructor
      · intro hw
        by_cases ht : w.2.2 = 0
        · exact mem_iUnion.2 ⟨some (idx ⟨w, hw⟩), memD _ w (hidx ⟨w, hw⟩) ht⟩
        · exact mem_iUnion.2 ⟨none, hw, ht⟩
      · intro hw
        obtain ⟨o, ho⟩ := mem_iUnion.1 hw
        exact hpsub o ho
    have hgn : bgnFinite K F n (differenceDomain K U) g := by
      refine ih (differenceDomain K U) (g66k_open hU) g piece hpopen hpsub hpcover ?_
      intro o
      cases o with
      | none =>
        have e : (fun x : puncturedDifferenceDomain K U => g ⟨x.val, hpsub none x.property⟩) =
            differenceQuotient K U f := by
          funext y
          simp only [g, dif_neg y.property.2]
        exact e ▸ hqn
      | some i =>
        have e : (fun x : differenceDomain K (Ui i) => g ⟨x.val, hpsub (some i) x.property⟩) = gi i := by
          funext y
          exact hA i y
        exact e ▸ hni i
    rw [g66k_succ]
    refine ⟨g66k_cont n _ _ hfn, g, hgc, ?_, hgn⟩
    intro z
    simp only [g, dif_neg z.property.2]

end G66L2

/-- Lemma 1.12, PDF pp.15–16: source C^k regularity is local on an arbitrary
open cover. The cover and the domain may be empty. -/
theorem solution
    (K : Type u) [Field K] [TopologicalSpace K] [T2Space K]
    [IsTopologicalDivisionRing K] (hK : ¬ DiscreteTopology K)
    (E : Type (max u v)) [AddCommGroup E] [Module K E] [TopologicalSpace E]
    [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul K E]
    (F : Type w) [AddCommGroup F] [Module K F] [TopologicalSpace F]
    [T2Space F] [IsTopologicalAddGroup F] [ContinuousSMul K F]
    (U : Set E) (hU : IsOpen U) (f : U → F) (k : WithTop ℕ)
    {I : Type*} (Ui : I → Set E) (hUi : ∀ i, IsOpen (Ui i))
    (hsub : ∀ i, Ui i ⊆ U) (hcover : U = ⋃ i, Ui i)
    (hlocal : ∀ i, bgnCr K F k (Ui i) (fun x => f ⟨x.val, hsub i x.property⟩)) :
    bgnCr K F k U f := by
  intro n hn
  exact g66l_loc (g66k_nebot hK) n U hU f Ui hUi hsub hcover (fun i => hlocal i n hn)

