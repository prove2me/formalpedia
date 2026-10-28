-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_simplegraph_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:22:22.70413+00:00
-- url     : https://prove2.me/submissions/39b832ce-744b-4a6d-bf07-94f9f41d47ff

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P R) :
    ∃ H : SimpleGraph V,
      R ≤ H ∧ P H ∧
      (∀ K : SimpleGraph V, H ≤ K → P K → K = H) := by
  classical
  let S : Finset (Finset (Sym2 V)) :=
    Finset.univ.filter fun e =>
      ∃ G : SimpleGraph V, R ≤ G ∧ P G ∧ G.edgeFinset = e
  have hRmem : R.edgeFinset ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨R, le_rfl, hP, rfl⟩
  let C : Finset ℕ := S.image fun e => e.card
  have hC : C.Nonempty := by
    refine ⟨R.edgeFinset.card, Finset.mem_image.mpr ?_⟩
    exact ⟨R.edgeFinset, hRmem, rfl⟩
  let n : ℕ := C.max' hC
  have hnmem : n ∈ C := by
    exact Finset.max'_mem C hC
  rcases Finset.mem_image.mp hnmem with ⟨e, heS, hecard⟩
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at heS
  obtain ⟨H, hRH, hPH, hHe⟩ := heS
  refine ⟨H, hRH, hPH, ?_⟩
  intro K hHK hPK
  by_contra hne
  have hlt : H < K := lt_of_le_of_ne hHK (Ne.symm hne)
  have hss : H.edgeFinset ⊂ K.edgeFinset :=
    (SimpleGraph.edgeFinset_ssubset_edgeFinset).2 hlt
  have hcardlt : H.edgeFinset.card < K.edgeFinset.card := Finset.card_lt_card hss
  have hKmem : K.edgeFinset ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨K, hRH.trans hHK, hPK, rfl⟩
  have hKmemC : K.edgeFinset.card ∈ C :=
    Finset.mem_image.mpr ⟨K.edgeFinset, hKmem, rfl⟩
  have hKle : K.edgeFinset.card ≤ n := by
    simpa [n] using Finset.le_max' C (K.edgeFinset.card) hKmemC
  rw [hHe] at hcardlt
  omega