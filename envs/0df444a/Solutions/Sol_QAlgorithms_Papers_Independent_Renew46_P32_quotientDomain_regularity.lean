-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P32.quotientDomain_regularity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:39:38.273982+00:00
-- url     : https://prove2.me/submissions/adf60385-9e2a-45e7-9e11-b50bd9f8b1c3

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

section G66D
variable {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]

theorem g66d_ck_congr {F : Type v} [AddCommGroup F] [Module K F] [TopologicalSpace F] (n : ℕ)
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


theorem g66d_neBot (hND : ¬ DiscreteTopology K) : NeBot (𝓝[≠] (0 : K)) := by
  rw [neBot_iff]
  intro h
  apply hND
  rw [discreteTopology_iff_isOpen_singleton_zero, isOpen_singleton_iff_punctured_nhds]
  exact h

theorem g66d_jet_open {E : Type u} [AddCommGroup E] [Module K E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul K E] (U : Set E) (hU : IsOpen U) :
    IsOpen (jetDomain (K := K) U) := by
  unfold jetDomain
  apply IsOpen.inter
  · exact hU.preimage continuous_fst
  · exact hU.preimage (continuous_fst.add
      ((continuous_snd.comp continuous_snd).smul (continuous_fst.comp continuous_snd)))

theorem g66d_cont0 {E E' : Type u} [TopologicalSpace E] [TopologicalSpace E'] {F : Type v}
    [TopologicalSpace F] (π : E → E') (hc : Continuous π) (ho : IsOpenMap π)
    (U : Set E) (hU : IsOpen U) (f : E' → F) :
    ContinuousOn f (π '' U) ↔ ContinuousOn (fun x => f (π x)) U := by
  constructor
  · intro h
    exact h.comp hc.continuousOn (Set.mapsTo_image π U)
  · intro h
    rintro _ ⟨x, hx, rfl⟩
    have h2 : Tendsto (fun x => f (π x)) (𝓝 x) (𝓝 (f (π x))) := (h x hx).continuousAt (hU.mem_nhds hx)
    have h3 : Tendsto f (map π (𝓝 x)) (𝓝 (f (π x))) := tendsto_map'_iff.mpr h2
    exact ContinuousAt.continuousWithinAt (h3.mono_left (ho.nhds_le x))

theorem g66d_main {F : Type v} [AddCommGroup F] [Module K F] [TopologicalSpace F] [T2Space F]
    (hNe : NeBot (𝓝[≠] (0 : K))) (n : ℕ) :
    ∀ {E E' : Type u} [AddCommGroup E] [Module K E] [TopologicalSpace E] [IsTopologicalAddGroup E]
      [ContinuousSMul K E] [AddCommGroup E'] [Module K E'] [TopologicalSpace E']
      (π : E →ₗ[K] E') (hc : Continuous π) (ho : IsOpenMap π) (hs : Function.Surjective π)
      (U : Set E) (hU : IsOpen U) (f : E' → F),
      fieldCk (K := K) n (π '' U) f ↔ fieldCk (K := K) n U (fun x => f (π x)) := by
  induction n with
  | zero =>
    intro E E' _ _ _ _ _ _ _ _ π hc ho hs U hU f
    rw [g66b_ck_zero, g66b_ck_zero]
    exact g66d_cont0 π hc ho U hU f
  | succ n ih =>
    intro E E' _ _ _ _ _ _ _ _ π hc ho hs U hU f
    let P : (E × E × K) →ₗ[K] (E' × E' × K) := π.prodMap (π.prodMap LinearMap.id)
    have hPapp : ∀ z : E × E × K, P z = (π z.1, π z.2.1, z.2.2) := fun z => rfl
    have hPc : Continuous P := by
      change Continuous (fun z : E × E × K => (π z.1, π z.2.1, z.2.2))
      exact (hc.comp continuous_fst).prodMk ((hc.comp (continuous_fst.comp continuous_snd)).prodMk
        (continuous_snd.comp continuous_snd))
    have hPo : IsOpenMap P := by
      change IsOpenMap (Prod.map π (Prod.map π id))
      exact ho.prodMap (ho.prodMap IsOpenMap.id)
    have hPs : Function.Surjective P := by
      change Function.Surjective (Prod.map π (Prod.map π id))
      exact hs.prodMap (hs.prodMap Function.surjective_id)
    have hJo := g66d_jet_open (K := K) U hU
    have himg : P '' jetDomain (K := K) U = jetDomain (K := K) (π '' U) := by
      ext ⟨x', v', t⟩
      simp only [Set.mem_image, jetDomain, Set.mem_setOf_eq, hPapp, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨x, v, s⟩, ⟨hx, hxv⟩, rfl, rfl, rfl⟩
        refine ⟨⟨x, hx, rfl⟩, ⟨x + s • v, hxv, ?_⟩⟩
        simp [map_add, map_smul]
      · rintro ⟨⟨x, hx, rfl⟩, ⟨y, hy, hyeq⟩⟩
        by_cases ht : t = 0
        · subst ht
          obtain ⟨v, rfl⟩ := hs v'
          exact ⟨(x, v, 0), ⟨hx, by simpa using hx⟩, rfl, rfl, rfl⟩
        · refine ⟨(x, t⁻¹ • (y - x), t), ⟨hx, ?_⟩, rfl, ?_, rfl⟩
          · simp only [smul_smul, mul_inv_cancel₀ ht, one_smul, add_sub_cancel]; exact hy
          · simp only [map_smul, map_sub, hyeq, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht,
              one_smul]
    rw [g66b_ck_succ, g66b_ck_succ, g66d_cont0 π hc ho U hU f, ← himg]
    constructor
    · rintro ⟨hcf, g, hg, hid⟩
      refine ⟨hcf, fun z => g (P z), (ih P hPc hPo hPs _ hJo g).mp hg, fun z hz => ?_⟩
      have := hid (P z) ⟨z, hz, rfl⟩
      simpa [hPapp, map_add, map_smul] using this
    · rintro ⟨hcf, g, hg, hid⟩
      have hgc : ContinuousOn g (jetDomain (K := K) U) := g66b_ck_cont n _ g hg
      -- nonzero t
      have hnz : ∀ z1 ∈ jetDomain (K := K) U, ∀ z2 ∈ jetDomain (K := K) U, P z1 = P z2 →
          z1.2.2 ≠ 0 → g z1 = g z2 := by
        intro z1 h1 z2 h2 he ht
        have e := congrArg (fun w : E' × E' × K => f (w.1 + w.2.2 • w.2.1) - f w.1) he
        simp only [hPapp] at e
        have e1 := hid z1 h1
        have e2 := hid z2 h2
        have ht2 : z2.2.2 = z1.2.2 := by
          have := congrArg (fun w : E' × E' × K => w.2.2) he; simpa [hPapp] using this.symm
        have q1 : f (π z1.1) + z1.2.2 • f 0 = f (π z1.1) + z1.2.2 • f 0 := rfl
        clear q1
        have k1 : f (π z1.1 + z1.2.2 • π z1.2.1) - f (π z1.1) = z1.2.2 • g z1 := by
          simpa [map_add, map_smul] using e1
        have k2 : f (π z2.1 + z2.2.2 • π z2.2.1) - f (π z2.1) = z2.2.2 • g z2 := by
          simpa [map_add, map_smul] using e2
        rw [e, k2, ht2] at k1
        exact (smul_right_injective F ht k1).symm
      have hfib : ∀ z1 ∈ jetDomain (K := K) U, ∀ z2 ∈ jetDomain (K := K) U, P z1 = P z2 →
          g z1 = g z2 := by
        intro z1 h1 z2 h2 he
        by_cases ht : z1.2.2 = 0
        · obtain ⟨x1, v1, t1⟩ := z1
          obtain ⟨x2, v2, t2⟩ := z2
          simp only at ht; subst ht
          have ht2 : t2 = 0 := by
            have := congrArg (fun w : E' × E' × K => w.2.2) he; simpa [hPapp] using this.symm
          subst ht2
          let γ1 : K → E × E × K := fun s => (x1, v1, s)
          let γ2 : K → E × E × K := fun s => (x2, v2, s)
          have hγ1 : Continuous γ1 := continuous_const.prodMk (continuous_const.prodMk continuous_id)
          have hγ2 : Continuous γ2 := continuous_const.prodMk (continuous_const.prodMk continuous_id)
          have T1 : Tendsto (fun s => g (γ1 s)) (𝓝[≠] 0) (𝓝 (g (x1, v1, 0))) :=
            ((hgc _ h1).continuousAt (hJo.mem_nhds h1)).tendsto.comp
              ((hγ1.tendsto 0).mono_left nhdsWithin_le_nhds)
          have T2 : Tendsto (fun s => g (γ2 s)) (𝓝[≠] 0) (𝓝 (g (x2, v2, 0))) :=
            ((hgc _ h2).continuousAt (hJo.mem_nhds h2)).tendsto.comp
              ((hγ2.tendsto 0).mono_left nhdsWithin_le_nhds)
          have E1 : ∀ᶠ s in 𝓝[≠] (0 : K), γ1 s ∈ jetDomain (K := K) U :=
            ((hγ1.tendsto 0).mono_left nhdsWithin_le_nhds).eventually (hJo.mem_nhds h1)
          have E2 : ∀ᶠ s in 𝓝[≠] (0 : K), γ2 s ∈ jetDomain (K := K) U :=
            ((hγ2.tendsto 0).mono_left nhdsWithin_le_nhds).eventually (hJo.mem_nhds h2)
          have E3 : ∀ᶠ s in 𝓝[≠] (0 : K), s ≠ 0 := self_mem_nhdsWithin
          have heq : (fun s => g (γ1 s)) =ᶠ[𝓝[≠] (0 : K)] (fun s => g (γ2 s)) := by
            filter_upwards [E1, E2, E3] with s hs1 hs2 hs3
            refine hnz _ hs1 _ hs2 ?_ hs3
            have := congrArg (fun w : E' × E' × K => (w.1, w.2.1)) he
            simp only [hPapp, Prod.mk.injEq] at this
            simp [γ1, γ2, hPapp, this.1, this.2]
          exact tendsto_nhds_unique (T1.congr' heq) T2
        · exact hnz z1 h1 z2 h2 he ht
      classical
      let g' : E' × E' × K → F := fun w =>
        if h : ∃ z ∈ jetDomain (K := K) U, P z = w then g h.choose else 0
      have hg' : ∀ z ∈ jetDomain (K := K) U, g' (P z) = g z := by
        intro z hz
        have h : ∃ z' ∈ jetDomain (K := K) U, P z' = P z := ⟨z, hz, rfl⟩
        simp only [g', dif_pos h]
        exact hfib _ h.choose_spec.1 _ hz h.choose_spec.2
      refine ⟨hcf, g', (ih P hPc hPo hPs _ hJo g').mpr
        (g66d_ck_congr n _ g _ hg fun z hz => (hg' z hz).symm), ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      rw [hg' z hz]
      simpa [hPapp, map_add, map_smul] using hid z hz

end G66D

theorem solution
    {K : Type} [Field K] [TopologicalSpace K]
    [IsTopologicalDivisionRing K] [T2Space K] (hNonDiscrete : ¬ DiscreteTopology K)
    {E : Type u} [AddCommGroup E] [Module K E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul K E] [T2Space E]
    {F : Type v} [AddCommGroup F] [Module K F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul K F] [T2Space F]
    (N : Submodule K E) (hN : IsClosed (N : Set E))
    (U : Set E) (hU : IsOpen U) (V : Set (E ⧸ N)) (hV : IsOpen V)
    (hImage : (fun x : E => (N.mkQ x : E ⧸ N)) '' U = V)
    (f : (E ⧸ N) → F) (r : WithTop ℕ) :
    fieldCr (K := K) r V f ↔
      fieldCr (K := K) r U (fun x => f (N.mkQ x)) := by
  have hNe := g66d_neBot hNonDiscrete
  subst hImage
  unfold fieldCr
  refine forall_congr' fun n => imp_congr_right fun _ => ?_
  exact g66d_main hNe n N.mkQ N.continuous_mkQ N.isOpenMap_mkQ N.mkQ_surjective U hU f
