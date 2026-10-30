-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph__p2m_9eedc9cb_93e3_43ae_9b38_877bad90d9bc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:39:26.708966+00:00
-- url     : https://prove2.me/submissions/7bb12d7f-ad26-46ca-87ef-2df3a8a96fd0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_finset_maximal_element__p2m_e3d00913_05dd_434d_bc2d_b9a3208fb1a4_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ (K : SimpleGraph V) (_ : DecidableRel K.Adj),
      H.edgeFinset ⊆ K.edgeFinset ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ (L : SimpleGraph V) (_ : DecidableRel L.Adj),
        K.edgeFinset ⊂ L.edgeFinset → ¬ WilliamsonShmoys.HasPlanarDrawingOn L := by
  classical
  let feasible : Finset (Sym2 V) → Prop := fun s =>
    ∃ K : SimpleGraph V,
      H.edgeFinset ⊆ s ∧ K.edgeFinset = s ∧
        WilliamsonShmoys.HasPlanarDrawingOn K
  have hfeasible : feasible H.edgeFinset := by
    refine ⟨H, Finset.Subset.rfl, ?_, hH⟩
    ext e
    simp
  obtain ⟨s, hs, hsmax⟩ :=
    finite_finset_maximal_element__p2m_e3d00913_05dd_434d_bc2d_b9a3208fb1a4_a1
      feasible H.edgeFinset hfeasible
  rcases hs with ⟨K, hHK, hKs, hKplanar⟩
  refine ⟨K, inferInstance, ?_, hKplanar, ?_⟩
  · simpa [hKs] using hHK
  · intro L _ hKL hLplanar
    apply hsmax L.edgeFinset
    · simpa [hKs] using hKL
    · refine ⟨L, ?_, ?_, hLplanar⟩
      · exact Finset.Subset.trans hHK (by simpa [hKs] using hKL.1)
      · ext e
        simp
