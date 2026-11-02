-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_5ca561e0_6863_43fe_aa41_85fb9a3351ed_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:46:39.526545+00:00
-- url     : https://prove2.me/submissions/2d3dc0a1-a101-4367-9bf3-dfcdb6c3b0e0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_predicate_maximal__p2m_93fb4221_4029_4870_92af_deed270da66d_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    letI : forall K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    exists K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K /\ J <= K /\
      forall L : SimpleGraph V,
        K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L = K := by
  classical
  letI : forall K : SimpleGraph V, DecidableRel K.Adj := fun K => Classical.decRel K.Adj
  let P : SimpleGraph V → Prop := fun K => HasPlanarDrawingOn K ∧ J ≤ K
  obtain ⟨K, hK, hmax⟩ :=
    WilliamsonShmoys.finite_predicate_maximal__p2m_93fb4221_4029_4870_92af_deed270da66d_a1
      (α := SimpleGraph V) P ⟨J, hJ, le_rfl⟩
  refine ⟨K, hK.1, hK.2, ?_⟩
  intro L hKL hL
  apply hmax L ⟨hL, le_trans hK.2 hKL⟩ hKL