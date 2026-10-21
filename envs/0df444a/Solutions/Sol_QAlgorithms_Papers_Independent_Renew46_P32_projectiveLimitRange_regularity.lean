-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P32.projectiveLimitRange_regularity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:27:15.969063+00:00
-- url     : https://prove2.me/submissions/83cefc88-4ea3-4bd1-925f-906498444202

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P32

open QAlgorithms.Papers.Independent.Renew46.P32

open Set Filter Topology

universe u v

section G66B
variable {K : Type} [Field K] [TopologicalSpace K]

theorem g66b_ck_succ (n : ℕ) {E : Type u} [AddCommGroup E] [Module K E] [TopologicalSpace E]
    {F : Type v} [AddCommGroup F] [Module K F] [TopologicalSpace F] (U : Set E) (f : E → F) :
    fieldCk (K := K) (n + 1) U f ↔ ContinuousOn f U ∧
      ∃ g : (E × E × K) → F, fieldCk (K := K) n (jetDomain (K := K) U) g ∧
        ∀ z ∈ jetDomain (K := K) U, f (z.1 + z.2.2 • z.2.1) - f z.1 = z.2.2 • g z := by
  rw [fieldCk]

theorem g66b_ck_zero {E : Type u} [AddCommGroup E] [Module K E] [TopologicalSpace E]
    {F : Type v} [AddCommGroup F] [Module K F] [TopologicalSpace F] (U : Set E) (f : E → F) :
    fieldCk (K := K) 0 U f ↔ ContinuousOn f U := by
  rw [fieldCk]

theorem g66b_ck_cont (n : ℕ) {E : Type u} [AddCommGroup E] [Module K E] [TopologicalSpace E]
    {F : Type v} [AddCommGroup F] [Module K F] [TopologicalSpace F] (U : Set E) (f : E → F)
    (h : fieldCk (K := K) n U f) : ContinuousOn f U := by
  cases n with
  | zero => exact (g66b_ck_zero U f).mp h
  | succ n => exact ((g66b_ck_succ n U f).mp h).1

end G66B

section G66B2
variable {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]

theorem g66b_neBot (hND : ¬ DiscreteTopology K) : NeBot (𝓝[≠] (0 : K)) := by
  rw [neBot_iff]
  intro h
  apply hND
  rw [discreteTopology_iff_isOpen_singleton_zero, isOpen_singleton_iff_punctured_nhds]
  exact h

theorem g66b_jet_open {E : Type u} [AddCommGroup E] [Module K E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul K E] (U : Set E) (hU : IsOpen U) :
    IsOpen (jetDomain (K := K) U) := by
  unfold jetDomain
  apply IsOpen.inter
  · exact hU.preimage continuous_fst
  · exact hU.preimage (continuous_fst.add
      ((continuous_snd.comp continuous_snd).smul (continuous_fst.comp continuous_snd)))

theorem g66b_cores_cont {E : Type u} [TopologicalSpace E] {F : Type v} [AddCommGroup F]
    [Module K F] [TopologicalSpace F] [AddCommGroup E] [Module K E]
    (S : Submodule K F) (U : Set E) (f : E → F) (hf : ∀ x ∈ U, f x ∈ S)
    (hc : ContinuousOn f U) : ContinuousOn (subspaceCorestriction S U f hf) U := by
  rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
  refine hc.congr fun x hx => ?_
  simp [subspaceCorestriction, hx]

theorem g66b_ck_cores {F : Type v} [AddCommGroup F] [Module K F] [TopologicalSpace F]
    (S : Submodule K F)
    (hmem : ∀ (φ : K → F) (y : F), Tendsto φ (𝓝[≠] 0) (𝓝 y) →
      (∀ᶠ t in 𝓝[≠] 0, φ t ∈ S) → y ∈ S) (n : ℕ) :
    ∀ {E : Type u} [AddCommGroup E] [Module K E] [TopologicalSpace E]
      [IsTopologicalAddGroup E] [ContinuousSMul K E]
      (U : Set E) (hU : IsOpen U) (f : E → F) (hf : ∀ x ∈ U, f x ∈ S),
      fieldCk (K := K) n U f → fieldCk (K := K) n U (subspaceCorestriction S U f hf) := by
  induction n with
  | zero =>
    intro E _ _ _ _ _ U hU f hf h
    rw [g66b_ck_zero] at h ⊢
    exact g66b_cores_cont S U f hf h
  | succ n ih =>
    intro E _ _ _ _ _ U hU f hf h
    rw [g66b_ck_succ] at h ⊢
    obtain ⟨hc, g, hg, hid⟩ := h
    have hJ := g66b_jet_open (K := K) U hU
    have hnz : ∀ z ∈ jetDomain (K := K) U, z.2.2 ≠ 0 → g z ∈ S := by
      intro z hz ht
      have e : g z = z.2.2⁻¹ • (f (z.1 + z.2.2 • z.2.1) - f z.1) := by
        rw [hid z hz, smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [e]
      exact S.smul_mem _ (S.sub_mem (hf _ hz.2) (hf _ hz.1))
    have hgS : ∀ z ∈ jetDomain (K := K) U, g z ∈ S := by
      rintro ⟨x, v, t⟩ hz
      by_cases ht : t = 0
      · subst ht
        have hgc : ContinuousAt g (x, v, 0) :=
          (g66b_ck_cont n _ g hg).continuousAt (hJ.mem_nhds hz)
        have hcurve : Continuous fun s : K => ((x, v, s) : E × E × K) := by fun_prop
        have ht1 : Tendsto (fun s : K => g (x, v, s)) (𝓝 0) (𝓝 (g (x, v, 0))) :=
          hgc.tendsto.comp (hcurve.tendsto' 0 _ rfl)
        apply hmem _ _ (ht1.mono_left nhdsWithin_le_nhds)
        have hev : ∀ᶠ s in 𝓝 (0 : K), ((x, v, s) : E × E × K) ∈ jetDomain (K := K) U :=
          hcurve.continuousAt.preimage_mem_nhds (hJ.mem_nhds hz)
        filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with s hs hs0
        exact hnz _ hs hs0
      · exact hnz _ hz ht
    refine ⟨g66b_cores_cont S U f hf hc, subspaceCorestriction S (jetDomain (K := K) U) g hgS,
      ih _ hJ g hgS hg, fun z hz => ?_⟩
    apply Subtype.ext
    simp [subspaceCorestriction, hz, hz.1, hz.2]
    exact hid z hz
end G66B2
section G66BP
variable {K : Type} [Field K] [TopologicalSpace K]
theorem g66b_ck_pi {I : Type u} {F : I → Type u}
    [∀ i, AddCommGroup (F i)] [∀ i, Module K (F i)] [∀ i, TopologicalSpace (F i)] (n : ℕ) :
    ∀ {E : Type u} [AddCommGroup E] [Module K E] [TopologicalSpace E]
      (U : Set E) (f : E → ∀ i, F i),
      fieldCk (K := K) n U f ↔ ∀ i, fieldCk (K := K) n U (fun x => f x i) := by
  induction n with
  | zero =>
    intro E _ _ _ U f
    simp only [g66b_ck_zero]
    exact continuousOn_pi
  | succ n ih =>
    intro E _ _ _ U f
    simp only [g66b_ck_succ]
    constructor
    · rintro ⟨hc, g, hg, hid⟩ i
      refine ⟨continuousOn_pi.mp hc i, fun z => g z i, (ih _ g).mp hg i, fun z hz => ?_⟩
      have := congrFun (hid z hz) i
      simpa using this
    · intro H
      choose hc g hg hid using H
      refine ⟨continuousOn_pi.mpr hc, fun z i => g i z, (ih _ _).mpr hg, fun z hz => ?_⟩
      funext i
      simpa using hid i z hz

end G66BP

section G66B3
variable {K : Type} [Field K] [TopologicalSpace K]

theorem g66b_ck_comp {F : Type v} [AddCommGroup F] [Module K F] [TopologicalSpace F]
    {G : Type v} [AddCommGroup G] [Module K G] [TopologicalSpace G]
    (L : F →ₗ[K] G) (hL : Continuous L) (n : ℕ) :
    ∀ {E : Type u} [AddCommGroup E] [Module K E] [TopologicalSpace E] (U : Set E) (f : E → F),
      fieldCk (K := K) n U f → fieldCk (K := K) n U (fun x => L (f x)) := by
  induction n with
  | zero =>
    intro E _ _ _ U f h
    rw [g66b_ck_zero] at h ⊢
    exact hL.comp_continuousOn h
  | succ n ih =>
    intro E _ _ _ U f h
    rw [g66b_ck_succ] at h ⊢
    obtain ⟨hc, g, hg, hid⟩ := h
    refine ⟨hL.comp_continuousOn hc, fun z => L (g z), ih _ g hg, fun z hz => ?_⟩
    rw [← map_sub, hid z hz, map_smul]

theorem g66b_ck_congr {F : Type v} [AddCommGroup F] [Module K F] [TopologicalSpace F] (n : ℕ)
    {E : Type u} [AddCommGroup E] [Module K E] [TopologicalSpace E] (U : Set E) (f f' : E → F)
    (h : fieldCk (K := K) n U f) (hff : ∀ x ∈ U, f x = f' x) : fieldCk (K := K) n U f' := by
  cases n with
  | zero =>
    rw [g66b_ck_zero] at h ⊢
    exact h.congr fun x hx => (hff x hx).symm
  | succ n =>
    rw [g66b_ck_succ] at h ⊢
    obtain ⟨hc, g, hg, hid⟩ := h
    refine ⟨hc.congr fun x hx => (hff x hx).symm, g, hg, fun z hz => ?_⟩
    rw [← hff _ hz.1, ← hff _ hz.2]
    exact hid z hz
end G66B3

theorem solution
    {K : Type} [Field K] [TopologicalSpace K]
    [IsTopologicalDivisionRing K] [T2Space K] (hNonDiscrete : ¬ DiscreteTopology K)
    {E : Type u} [AddCommGroup E] [Module K E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul K E] [T2Space E]
    {I : Type u} [Preorder I] [IsDirectedOrder I]
    {F : I → Type u} [∀ i, AddCommGroup (F i)] [∀ i, Module K (F i)]
    [∀ i, TopologicalSpace (F i)] [∀ i, IsTopologicalAddGroup (F i)]
    [∀ i, ContinuousSMul K (F i)] [∀ i, T2Space (F i)]
    (bond : ∀ i j : I, i ≤ j → F j →ₗ[K] F i)
    (hCont : ∀ i j h, Continuous (bond i j h))
    (hId : ∀ i, bond i i le_rfl = LinearMap.id)
    (hComp : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k),
      bond i k (le_trans hij hjk) = (bond i j hij).comp (bond j k hjk))
    (U : Set E) (hU : IsOpen U) (f : E → projectiveLimitSubmodule bond)
    (r : WithTop ℕ) :
    fieldCr (K := K) r U f ↔
      ∀ i, fieldCr (K := K) r U (fun x => (f x).val i) := by
  unfold fieldCr
  constructor
  · intro h i n hn
    let L : (projectiveLimitSubmodule bond) →ₗ[K] F i := (LinearMap.proj i).comp (projectiveLimitSubmodule bond).subtype
    have hL : Continuous L := (continuous_apply i).comp continuous_subtype_val
    exact g66b_ck_comp L hL n U f (h n hn)
  · intro h n hn
    have hP : fieldCk (K := K) n U (fun x => (f x).val) :=
      (g66b_ck_pi n U (fun x => (f x).val)).mpr fun i => h i n hn
    have hSc : IsClosed ((projectiveLimitSubmodule bond) : Set (∀ i, F i)) := by
      have : ((projectiveLimitSubmodule bond) : Set (∀ i, F i)) =
          ⋂ i, ⋂ j, ⋂ hij : i ≤ j, {a | bond i j hij (a j) = a i} := by
        ext a; simp only [Set.mem_iInter, Set.mem_setOf_eq]; rfl
      rw [this]
      exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun hij =>
        isClosed_eq ((hCont i j hij).comp (continuous_apply j)) (continuous_apply i)
    have hmem : ∀ (φ : K → (∀ i, F i)) (y : ∀ i, F i), Tendsto φ (𝓝[≠] 0) (𝓝 y) →
        (∀ᶠ t in 𝓝[≠] 0, φ t ∈ (projectiveLimitSubmodule bond)) → y ∈ (projectiveLimitSubmodule bond) := by
      haveI := g66b_neBot hNonDiscrete
      intro φ y hφ hev
      exact hSc.mem_of_tendsto hφ hev
    have hI : ∀ x ∈ U, (f x).val ∈ (projectiveLimitSubmodule bond) := fun x _ => (f x).2
    have := g66b_ck_cores (projectiveLimitSubmodule bond) hmem n U hU (fun x => (f x).val) hI hP
    refine g66b_ck_congr n U _ _ this fun x hx => ?_
    apply Subtype.ext
    simp [subspaceCorestriction, hx]
