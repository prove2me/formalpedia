-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_supergraph__p2m_b48f5d89_dd8c_44de_b172_78fd0037e2dc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:03:18.207694+00:00
-- url     : https://prove2.me/submissions/acee1c1d-857c-4404-9dfd-ce7285236578

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open Finset


theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (P : SimpleGraph V → Prop)
    (hP : P K)
    (hconn : K.Connected) :
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      (letI : DecidableRel H.Adj := dH
       K ≤ H ∧ H.Connected ∧ P H ∧
       (∀ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
         (letI : DecidableRel L.Adj := dL
          H ≤ L → P L → L ≤ H)) ∧
       K.edgeFinset.card ≤ H.edgeFinset.card) := by
  classical
  let Q : SimpleGraph V → Prop := fun G => K ≤ G ∧ P G
  obtain ⟨H, dH, hExt⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists Q).2 ⟨K, le_rfl, hP⟩
  refine ⟨H, dH, ?_⟩
  letI : DecidableRel H.Adj := dH
  have hKH : K ≤ H := hExt.1.1
  have hPH : P H := hExt.1.2
  refine ⟨hKH, hconn.mono hKH, hPH, ?_, ?_⟩
  · intro L dL hHL hPL
    letI : DecidableRel L.Adj := dL
    have hKL : K ≤ L := le_trans hKH hHL
    have hcard : L.edgeFinset.card ≤ H.edgeFinset.card :=
      hExt.2 ⟨hKL, hPL⟩
    have hEq : H.edgeFinset = L.edgeFinset :=
      Finset.eq_of_subset_of_card_le
        (SimpleGraph.edgeFinset_subset_edgeFinset.mpr hHL) hcard
    exact le_of_eq (SimpleGraph.edgeFinset_inj.mp hEq).symm
  · exact Finset.card_le_card (SimpleGraph.edgeFinset_subset_edgeFinset.mpr hKH)

