-- Prove2me | solution 1 for SocialEquilibrium.Existence.bestValue_lowerSemicontinuousAt
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:18:27.29415+00:00
-- url     : https://prove2.me/submissions/e04fccf9-6f02-4abe-af42-666f58fb58e5

import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_graph
import Definitions.Def_SocialEquilibrium_Existence_Game

namespace SocialEquilibrium.Existence

end SocialEquilibrium.Existence

open SocialEquilibrium.Existence

open Filter Topology
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (X : ∀ i, Set (E i)) (A : ∀ i : ι, Others X i → Set (X i))
    (f : ι → (∀ j, X j) → EReal) (i : ι) (ā₀ : Others X i)
    (hA : ∀ ā : Others X i, (A i ā).Nonempty)
    (hG : IsCompact (graph (A i)))
    (hf : ContinuousOn (fun p : Others X i × X i => f i (join X i p.1 p.2)) (graph (A i)))
    (hAc : ConstraintContinuousAt A i ā₀) :
    LowerSemicontinuousAt (bestValue X A f i) ā₀ := by
  intro y hy
  -- pick b ∈ A i ā₀ with y < f(ā₀, b)
  obtain ⟨v, ⟨b, hb, rfl⟩, hyv⟩ := (lt_sSup_iff).1 hy
  by_contra hne
  rw [Filter.not_eventually] at hne
  have hne' : ∃ᶠ ā in 𝓝 ā₀, bestValue X A f i ā ≤ y := by
    refine hne.mono ?_
    intro ā h
    exact not_lt.1 h
  obtain ⟨s, hs, hsy⟩ := Filter.exists_seq_forall_of_frequently hne'
  obtain ⟨a, ha, haA⟩ := hAc b hb s hs
  have hgraph : ((ā₀, b) : Others X i × X i) ∈ graph (A i) := hb
  have htend : Tendsto (fun n => ((s n, a n) : Others X i × X i)) atTop
      (𝓝[graph (A i)] (ā₀, b)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hs.prodMk_nhds ha, Eventually.of_forall ?_⟩
    intro n
    exact haA n
  have hc := (hf (ā₀, b) hgraph).tendsto.comp htend
  obtain ⟨n, hn⟩ := (hc.eventually (lt_mem_nhds hyv)).exists
  have hle : f i (join X i (s n) (a n)) ≤ bestValue X A f i (s n) :=
    le_sSup ⟨a n, haA n, rfl⟩
  exact absurd (lt_of_lt_of_le hn (le_trans hle (hsy n))) (lt_irrefl y)
