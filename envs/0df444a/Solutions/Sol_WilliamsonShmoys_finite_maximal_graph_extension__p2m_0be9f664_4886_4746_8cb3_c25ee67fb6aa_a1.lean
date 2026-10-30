-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_graph_extension__p2m_0be9f664_4886_4746_8cb3_c25ee67fb6aa_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:32:45.323984+00:00
-- url     : https://prove2.me/submissions/24ae42e0-e6f2-479b-ba34-2b78e5da0c64

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open SimpleGraph

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P M) :
    ∃ K : SimpleGraph V, M ≤ K ∧ P K ∧
      ∀ L : SimpleGraph V, K ≤ L → P L → L = K := by
  classical
  let S : Type := {K : SimpleGraph V // M ≤ K ∧ P K}
  letI : PartialOrder S := inferInstance
  letI : Nonempty S := ⟨⟨M, le_rfl, hP⟩⟩
  have hfinite : Finite S := Finite.of_injective
    (fun K : S => K.1) Subtype.val_injective
  letI : Finite S := hfinite
  letI : Fintype S := Fintype.ofFinite S
  obtain ⟨K, hKmem, hKmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset S)
      (fun X : S => X.1.edgeFinset.card)
      (Finset.univ_nonempty_iff.mpr ⟨⟨M, le_rfl, hP⟩⟩)
  refine ⟨K.1, K.2.1, K.2.2, ?_⟩
  intro L hKL hPL
  let L' : S := ⟨L, le_trans K.2.1 hKL, hPL⟩
  have hmax : L'.1.edgeFinset.card ≤ K.1.edgeFinset.card :=
    hKmax L' (Finset.mem_univ _)
  by_contra hne
  have hneq : K.1 ≠ L := by
    intro heq
    exact hne heq.symm
  have hlt : K.1 < L := lt_of_le_of_ne hKL hneq
  have hcard : K.1.edgeFinset.card < L.edgeFinset.card :=
    Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
  change L.edgeFinset.card ≤ K.1.edgeFinset.card at hmax
  exact (not_lt_of_ge hmax hcard)