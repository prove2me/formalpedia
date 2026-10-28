-- Prove2me | solution 1 for WilliamsonShmoys.finite_hereditary_property_maximal_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T20:58:12.46544+00:00
-- url     : https://prove2.me/submissions/237526c5-b355-4d97-9719-95a44e301127

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite

set_option autoImplicit false

open Finset

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hhered : ∀ G H : SimpleGraph V, H ≤ G → P G → P H)
    (R : SimpleGraph V)
    (hR : P R) :
    ∃ S : SimpleGraph V,
      R ≤ S ∧ P S ∧
      ∀ T : SimpleGraph V, S ≤ T → P T → T = S := by
  classical
  let admissible : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => R ≤ G ∧ P G
  have hadm : admissible.Nonempty := by
    refine ⟨R, ?_⟩
    simp [admissible, hR]
  obtain ⟨S, hS_mem, hS_max⟩ :=
    Finset.exists_max_image admissible (fun G => G.edgeFinset.card) hadm
  have hS : R ≤ S ∧ P S := by
    simpa [admissible] using hS_mem
  refine ⟨S, hS.1, hS.2, ?_⟩
  intro T hST hT
  have hRT : R ≤ T := le_trans hS.1 hST
  have hT_mem : T ∈ admissible := by
    simp [admissible, hRT, hT]
  have hcard : T.edgeFinset.card ≤ S.edgeFinset.card := hS_max T hT_mem
  have heq : S.edgeFinset = T.edgeFinset :=
    Finset.eq_of_subset_of_card_le
      (SimpleGraph.edgeFinset_subset_edgeFinset.mpr hST) hcard
  exact (SimpleGraph.edgeFinset_inj.mp heq).symm