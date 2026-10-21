-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P28.assertion_1_8
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:38:49.607001+00:00
-- url     : https://prove2.me/submissions/929e72f0-2d1e-42f4-824c-02b52c172715

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

/-- Assertion 1.8, PDF p.14: continuous extension characterization, openness and
density of the punctured domain, disjoint zero-slice decomposition, and preservation
of every finite or infinite regularity order by the ordinary quotient map. -/
theorem solution
    (K : Type u) [Field K] [TopologicalSpace K] [T2Space K]
    [IsTopologicalDivisionRing K] (hK : ¬ DiscreteTopology K)
    (E : Type (max u v)) [AddCommGroup E] [Module K E] [TopologicalSpace E]
    [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul K E]
    (F : Type w) [AddCommGroup F] [Module K F] [TopologicalSpace F]
    [T2Space F] [IsTopologicalAddGroup F] [ContinuousSMul K F]
    (U : Set E) (hU : IsOpen U) (f : U → F) :
    (bgnCr K F 1 U f ↔ Continuous f ∧
      ∃ g : differenceDomain K U → F,
        Continuous g ∧ extendsDifferenceQuotient K U f g) ∧
    IsOpen (puncturedDifferenceDomain K U) ∧
    Dense {z : differenceDomain K U | z.val.2.2 ≠ 0} ∧
    differenceDomain K U = puncturedDifferenceDomain K U ∪
      {z : E × E × K | z.1 ∈ U ∧ z.2.2 = 0} ∧
    Disjoint (puncturedDifferenceDomain K U)
      {z : E × E × K | z.1 ∈ U ∧ z.2.2 = 0} ∧
    (∀ k : WithTop ℕ, bgnCr K F k U f →
      bgnCr K F k (puncturedDifferenceDomain K U) (differenceQuotient K U f)) := by
  have hD : IsOpen (differenceDomain K U) := g66k_open hU
  have hNe := g66k_nebot hK
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro h
      have h1 := h 1 le_rfl
      rw [g66k_succ] at h1
      obtain ⟨hc, g, hg, hext, _⟩ := h1
      exact ⟨hc, g, hg, hext⟩
    · rintro ⟨hc, g, hg, hext⟩ n hn
      have hn' : n ≤ 1 := by exact_mod_cast hn
      interval_cases n
      · rw [g66k_zero]; exact hc
      · rw [g66k_succ]; exact ⟨hc, g, hg, hext, (g66k_zero _ g).2 hg⟩
  · have : puncturedDifferenceDomain K U = differenceDomain K U ∩ {z | z.2.2 ≠ 0} := by
      ext z; simp [puncturedDifferenceDomain]
    rw [this]
    exact hD.inter (isOpen_compl_singleton.preimage (continuous_snd.comp continuous_snd))
  · intro z
    rw [closure_subtype]
    obtain ⟨⟨x, y, t⟩, hz⟩ := z
    by_cases ht : t = 0
    · subst ht
      have hι : Continuous fun s : K => (x, y, s) := by fun_prop
      have hev : ∀ᶠ s in 𝓝 (0 : K), (x, y, s) ∈ differenceDomain K U :=
        (hι.tendsto 0) (hD.mem_nhds hz)
      refine mem_closure_of_tendsto (f := fun s : K => (x, y, s)) (b := 𝓝[≠] (0 : K))
        ((hι.tendsto 0).mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with s hs hs0
      exact ⟨⟨(x, y, s), hs⟩, hs0, rfl⟩
    · exact subset_closure ⟨⟨(x, y, t), hz⟩, ht, rfl⟩
  · ext ⟨x, y, t⟩
    by_cases ht : t = 0
    · subst ht
      simp [differenceDomain, puncturedDifferenceDomain]
    · simp [differenceDomain, puncturedDifferenceDomain, ht]
  · rw [Set.disjoint_left]
    rintro z ⟨_, hz⟩ ⟨_, hz0⟩
    exact hz hz0
  · intro k hk n hn
    have hf := hk n hn
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

