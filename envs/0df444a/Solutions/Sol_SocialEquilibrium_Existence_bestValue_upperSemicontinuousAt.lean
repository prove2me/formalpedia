-- Prove2me | solution 1 for SocialEquilibrium.Existence.bestValue_upperSemicontinuousAt
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:12:27.648238+00:00
-- url     : https://prove2.me/submissions/8b3a73b3-0bc0-4ff7-a865-c6e3c2010b38

import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_graph
import Definitions.Def_SocialEquilibrium_Existence_Game

namespace SocialEquilibrium.Existence

end SocialEquilibrium.Existence

open SocialEquilibrium.Existence

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (X : ∀ i, Set (E i)) (A : ∀ i : ι, Others X i → Set (X i))
    (f : ι → (∀ j, X j) → EReal) (i : ι) (ā₀ : Others X i)
    (hA : ∀ ā : Others X i, (A i ā).Nonempty)
    (hG : IsCompact (graph (A i)))
    (hf : ContinuousOn (fun p : Others X i × X i => f i (join X i p.1 p.2)) (graph (A i))) :
    UpperSemicontinuousAt (bestValue X A f i) ā₀ := by
  intro y hy
  obtain ⟨z, hz1, hz2⟩ := exists_between hy
  have hK : IsCompact (graph (A i) ∩
      (fun p : Others X i × X i => f i (join X i p.1 p.2)) ⁻¹' Set.Ici z) := by
    apply hG.of_isClosed_subset _ Set.inter_subset_left
    exact hf.preimage_isClosed_of_isClosed hG.isClosed isClosed_Ici
  have hP : IsClosed (Prod.fst '' (graph (A i) ∩
      (fun p : Others X i × X i => f i (join X i p.1 p.2)) ⁻¹' Set.Ici z)) :=
    (hK.image continuous_fst).isClosed
  have hmem : ā₀ ∉ Prod.fst '' (graph (A i) ∩
      (fun p : Others X i × X i => f i (join X i p.1 p.2)) ⁻¹' Set.Ici z) := by
    rintro ⟨⟨a, b⟩, ⟨hb, hfz⟩, rfl⟩
    simp only [Set.mem_preimage, Set.mem_Ici] at hfz
    have hle : f i (join X i a b) ≤ bestValue X A f i a := le_sSup ⟨b, hb, rfl⟩
    exact absurd (lt_of_le_of_lt hle hz1) (not_lt.mpr hfz)
  filter_upwards [hP.isOpen_compl.mem_nhds hmem] with a ha
  apply lt_of_le_of_lt _ hz2
  apply sSup_le
  rintro _ ⟨b, hb, rfl⟩
  by_contra h
  exact ha ⟨(a, b), ⟨hb, (not_le.mp h).le⟩, rfl⟩
