-- Prove2me | solution 1 for Stanley.alternating_sources
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:16.528985+00:00
-- url     : https://prove2.me/submissions/92ff8b9d-c81a-44e9-8099-0bb7d4009385

module
public import Definitions.Def_Stanley_Orientation
public import Definitions.Def_Stanley_SourceSum
public import Theorems.Thm_Stanley_AcyclicOrientation_exists_source


set_option autoImplicit true
@[expose] public section
public section
open Stanley
open SimpleGraph Finset
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
open Classical
namespace Stanley
theorem _root_.solution [Nonempty V] :
    ∑ s : Finset V, (-1 : ℤ) ^ s.card *
      (Fintype.card {D : AcyclicOrientation G // D.AllSources (s : Set V)} : ℤ) = 0 := by
  classical
  have hcard (s : Finset V) :
      (Fintype.card {D : AcyclicOrientation G // D.AllSources (s : Set V)} : ℤ) =
        ∑ D : AcyclicOrientation G, if D.AllSources (s : Set V) then 1 else 0 := by
    simp [Fintype.card_subtype, Finset.sum_boole]
  simp_rw [hcard, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro D _
  let sources : Finset V := univ.filter D.Source
  have hsources : sources.Nonempty := by
    obtain ⟨v, hv⟩ := D.exists_source
    exact ⟨v, mem_filter.mpr ⟨mem_univ v, hv⟩⟩
  have hsets : univ.filter (fun s : Finset V => D.AllSources (s : Set V)) =
      sources.powerset := by
    ext s
    simp [AcyclicOrientation.AllSources, sources, Finset.subset_iff]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, hsets]
  exact Finset.sum_powerset_neg_one_pow_card_of_nonempty hsources
end Stanley
