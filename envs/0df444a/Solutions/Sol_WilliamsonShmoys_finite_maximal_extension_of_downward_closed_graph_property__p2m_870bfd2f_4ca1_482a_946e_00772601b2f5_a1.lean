-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_extension_of_downward_closed_graph_property__p2m_870bfd2f_4ca1_482a_946e_00772601b2f5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:46:47.139291+00:00
-- url     : https://prove2.me/submissions/ce1dedbf-bccd-46eb-b0d1-72f5ba7fb065

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Finite

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (M : SimpleGraph V)
    (Q : SimpleGraph V -> Prop)
    (hdown : forall G H : SimpleGraph V, LE.le G H -> Q H -> Q G)
    (hM : Q M) :
    Exists fun N : SimpleGraph V =>
      And (LE.le M N) (And (Q N)
        (forall P : SimpleGraph V, LE.le N P -> Q P -> P = N)) := by
  classical
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun G => LE.le M G ∧ Q G)
  have hMmem : M ∈ candidates := by
    simp [candidates, hM]
  obtain ⟨N, hNmem, hNmax⟩ :=
    Finset.exists_max_image candidates (fun G => G.edgeFinset.card) ⟨M, hMmem⟩
  have hMN : LE.le M N := (Finset.mem_filter.mp hNmem).2.1
  have hQN : Q N := (Finset.mem_filter.mp hNmem).2.2
  refine ⟨N, hMN, hQN, ?_⟩
  intro P hNP hQP
  by_contra hne
  have hMP : LE.le M P := le_trans hMN hNP
  have hPmem : P ∈ candidates := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ P, hMP, hQP⟩
  have hsubset : N.edgeFinset ⊆ P.edgeFinset :=
    SimpleGraph.edgeFinset_subset_edgeFinset.mpr hNP
  have hneq : ¬ N.edgeFinset = P.edgeFinset := by
    intro heq
    exact hne (SimpleGraph.edgeFinset_inj.mp heq).symm
  have hssub := Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, hneq⟩
  have hcard : N.edgeFinset.card < P.edgeFinset.card := Finset.card_lt_card hssub
  exact (not_lt_of_ge (hNmax P hPmem)) hcard