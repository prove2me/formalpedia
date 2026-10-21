-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P32.closedSubspace_corestriction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:25:54.850358+00:00
-- url     : https://prove2.me/submissions/5013593f-2b01-4f1c-aeaa-e817ea95c0f3

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
section TopologicalFieldResults

variable {K : Type} [Field K] [TopologicalSpace K]

variable [hKTop : IsTopologicalDivisionRing K] [hKT2 : T2Space K]

variable (hNonDiscrete : ¬ DiscreteTopology K)

variable {E : Type u} [AddCommGroup E] [Module K E] [TopologicalSpace E]

variable [hETop : IsTopologicalAddGroup E] [hESmul : ContinuousSMul K E] [hET2 : T2Space E]

variable {F : Type v} [AddCommGroup F] [Module K F] [TopologicalSpace F]

variable [hFTop : IsTopologicalAddGroup F] [hFSmul : ContinuousSMul K F] [hFT2 : T2Space F]

include hKTop hKT2 hNonDiscrete hETop hESmul hET2 hFTop hFSmul hFT2

/-- Lemma 10.1, PDF pp. 48--49: both closedness alternatives and every
finite order or infinity; the subspace has its induced topology. -/
theorem solution
    (U : Set E) (hU : IsOpen U) (f : E → F) (r : WithTop ℕ)
    (hf : fieldCr (K := K) r U f) (S : Submodule K F)
    (hImage : ∀ x ∈ U, f x ∈ S)
    (hClosed : IsClosed (S : Set F) ∨
      (IsSeqClosed (S : Set F) ∧ TopologicalSpace.MetrizableSpace K)) :
    fieldCr (K := K) r U (subspaceCorestriction S U f hImage) := by
  have hmem : ∀ (φ : K → F) (y : F), Tendsto φ (𝓝[≠] 0) (𝓝 y) →
      (∀ᶠ t in 𝓝[≠] 0, φ t ∈ S) → y ∈ S := by
    haveI := g66b_neBot hNonDiscrete
    intro φ y hφ hev
    rcases hClosed with hC | ⟨hC, hM⟩
    · exact hC.mem_of_tendsto hφ hev
    · obtain ⟨t, ht⟩ := exists_seq_tendsto (𝓝[≠] (0 : K))
      obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually hev)
      exact hC (x := fun n => φ (t (n + N))) (fun n => hN _ (by omega))
        ((hφ.comp ht).comp (tendsto_add_atTop_nat N))
  intro n hn
  exact g66b_ck_cores S hmem n U hU f hImage (hf n hn)

end TopologicalFieldResults
