-- Prove2me | solution 1 for SimpleGraph.exists_maximal_supergraph_of_downward_closed__p2m_407cedf5_8faa_4a1f_b011_cc5bdf645c63_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:51:47.968797+00:00
-- url     : https://prove2.me/submissions/b1f5b975-8865-4beb-a08d-dd2ee07269cf

import Mathlib

set_option autoImplicit false

open SimpleGraph

theorem solution {V : Type} [Fintype V] (P : SimpleGraph V → Prop)
    (hdown : ∀ ⦃H K : SimpleGraph V⦄, H ≤ K → P K → P H)
    (G : SimpleGraph V) (hG : P G) :
    ∃ J : SimpleGraph V, G ≤ J ∧ P J ∧
      ∀ K : SimpleGraph V, J ≤ K → P K → K = J := by
  classical
  let S : Set (SimpleGraph V) := {K | G ≤ K ∧ P K}
  have hS : S.Finite := Set.toFinite S
  have hSne : S.Nonempty := ⟨G, le_rfl, hG⟩
  obtain ⟨J, hJmem, hJmax⟩ :=
    Set.exists_max_image S (fun K : SimpleGraph V => K.edgeFinset.card) hS hSne
  refine ⟨J, hJmem.1, hJmem.2, ?_⟩
  intro K hJK hPK
  have hKmem : K ∈ S := ⟨le_trans hJmem.1 hJK, hPK⟩
  have hcard : K.edgeFinset.card ≤ J.edgeFinset.card := hJmax K hKmem
  have hsub : J.edgeFinset ⊆ K.edgeFinset :=
    edgeFinset_subset_edgeFinset.2 hJK
  have hedge : J.edgeFinset = K.edgeFinset :=
    Finset.eq_of_subset_of_card_le hsub hcard
  exact (edgeFinset_inj.1 hedge).symm