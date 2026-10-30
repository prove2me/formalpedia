-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_for_finite_property__p2m_d861cb11_4d1d_4208_9ad9_8ec6eefefc53_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:46:37.055822+00:00
-- url     : https://prove2.me/submissions/5f603610-f4ba-4936-b63b-cdde8086b6d5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : SimpleGraph V → Prop)
    (hG : P G) :
    ∃ H : SimpleGraph V, ∃ (_ : DecidableRel H.Adj),
      G.edgeFinset ⊆ H.edgeFinset ∧
      P H ∧
      ∀ K : SimpleGraph V,
        (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) →
        P K → K = H := by
  classical
  let S : Set (SimpleGraph V) := {H | P H ∧ G ≤ H}
  have hSfinite : S.Finite :=
    Set.Finite.subset Set.finite_univ (by
      intro H hH
      simp)
  have hSnonempty : S.Nonempty := by
    refine ⟨G, ?_⟩
    simp [S, hG]
  obtain ⟨H, hHmem, hHmax⟩ :=
    Set.exists_max_image S (fun X : SimpleGraph V => X.edgeFinset.card)
      hSfinite hSnonempty
  rcases hHmem with ⟨hPH, hGH⟩
  refine ⟨H, inferInstance, ?_⟩
  refine ⟨SimpleGraph.edgeFinset_subset_edgeFinset.2 hGH, hPH, ?_⟩
  intro K hHK hPK
  have hHK' : H ≤ K := hHK
  have hGK : G ≤ K := le_trans hGH hHK'
  have hKmem : K ∈ S := by
    simpa [S] using And.intro hPK hGK
  have hcard : K.edgeFinset.card ≤ H.edgeFinset.card := hHmax K hKmem
  have hsub : H.edgeFinset ⊆ K.edgeFinset :=
    SimpleGraph.edgeFinset_subset_edgeFinset.2 hHK'
  have hcard' : H.edgeFinset.card ≤ K.edgeFinset.card := Finset.card_le_card hsub
  have hcards : H.edgeFinset.card = K.edgeFinset.card := Nat.le_antisymm hcard' hcard
  have hedge : H.edgeFinset = K.edgeFinset :=
    Finset.eq_of_subset_of_card_le hsub (le_of_eq hcards.symm)
  exact SimpleGraph.edgeFinset_inj.1 hedge.symm