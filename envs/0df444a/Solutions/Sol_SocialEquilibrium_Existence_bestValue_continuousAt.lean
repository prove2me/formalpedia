-- Prove2me | solution 1 for SocialEquilibrium.Existence.bestValue_continuousAt
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T16:18:00.36251+00:00
-- url     : https://prove2.me/submissions/4b82d1a5-32d5-43b2-aaad-389be1e1bfb2

import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_graph
import Definitions.Def_SocialEquilibrium_Existence_Game

set_option autoImplicit false

open SocialEquilibrium.Existence Filter Topology in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (X : ∀ i, Set (E i)) (A : ∀ i : ι, Others X i → Set (X i))
    (f : ι → (∀ j, X j) → EReal) (i : ι) (ā₀ : Others X i)
    (hA : ∀ ā : Others X i, (A i ā).Nonempty)
    (hG : IsCompact (graph (A i)))
    (hf : ContinuousOn (fun p : Others X i × X i => f i (join X i p.1 p.2)) (graph (A i)))
    (hAc : ConstraintContinuousAt A i ā₀) :
    ContinuousAt (bestValue X A f i) ā₀ := by
  set g : Others X i × X i → EReal := fun p => f i (join X i p.1 p.2) with hg
  have hval : ∀ ā b, b ∈ A i ā → g (ā, b) ≤ bestValue X A f i ā := fun ā b hb =>
    le_sSup (Set.mem_image_of_mem _ hb)
  -- upper part: eventually φ < c
  have hup : ∀ c, bestValue X A f i ā₀ < c → ∀ᶠ ā in 𝓝 ā₀, bestValue X A f i ā < c := by
    intro c hc
    obtain ⟨c', hc1, hc2⟩ := exists_between hc
    have hS : IsClosed (graph (A i) ∩ g ⁻¹' Set.Ici c') :=
      hf.preimage_isClosed_of_isClosed hG.isClosed isClosed_Ici
    have hSc : IsCompact (graph (A i) ∩ g ⁻¹' Set.Ici c') :=
      hG.of_isClosed_subset hS Set.inter_subset_left
    have hK : IsClosed (Prod.fst '' (graph (A i) ∩ g ⁻¹' Set.Ici c')) :=
      (hSc.image continuous_fst).isClosed
    have hnot : ā₀ ∉ Prod.fst '' (graph (A i) ∩ g ⁻¹' Set.Ici c') := by
      rintro ⟨⟨a, b⟩, ⟨hgr, hge⟩, rfl⟩
      have h1 := hval a b hgr
      have h2 : c' ≤ g (a, b) := hge
      exact absurd (lt_of_le_of_lt (h2.trans h1) hc1) (lt_irrefl _)
    filter_upwards [hK.isOpen_compl.mem_nhds hnot] with ā hā
    refine lt_of_le_of_lt ?_ hc2
    refine sSup_le ?_
    rintro _ ⟨b, hb, rfl⟩
    exact (not_le.1 fun hge => hā ⟨(ā, b), ⟨hb, hge⟩, rfl⟩).le
  rw [ContinuousAt, tendsto_nhds_iff_seq_tendsto]
  intro u hu
  refine tendsto_order.2 ⟨fun c hc => ?_, fun c hc => (hu.eventually (hup c hc))⟩
  obtain ⟨_, ⟨b₀, hb₀, rfl⟩, hlt⟩ := lt_sSup_iff.1 hc
  obtain ⟨v, hv, hvA⟩ := hAc b₀ hb₀ u hu
  have hmem : (ā₀, b₀) ∈ graph (A i) := hb₀
  have ht : Tendsto (fun n => (u n, v n)) atTop (𝓝[graph (A i)] (ā₀, b₀)) :=
    tendsto_nhdsWithin_iff.2 ⟨hu.prodMk_nhds hv, Eventually.of_forall fun n => hvA n⟩
  have hgt : Tendsto (fun n => g (u n, v n)) atTop (𝓝 (g (ā₀, b₀))) :=
    (hf _ hmem).tendsto.comp ht
  filter_upwards [hgt.eventually (lt_mem_nhds hlt)] with n hn
  exact lt_of_lt_of_le hn (hval _ _ (hvA n))
