-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_euler_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T22:55:55.121977+00:00
-- url     : https://prove2.me/submissions/6c1ab837-fc1d-4544-a7da-adeb9c339b57

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_tight_planar_completion

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V, K <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    exists f : Nat,
      Fintype.card V + f = K.edgeSet.ncard + 2 /\
      3 * f = 2 * K.edgeSet.ncard := by
  rcases WilliamsonShmoys.drawable_graph_has_tight_planar_completion
      K hK hV with ⟨L, hKL, hL, hcount⟩
  have hLK : L = K := hmax L hKL hL
  have hcountK : K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
    simpa [hLK] using hcount
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩
  · rw [hcountK]
    omega
  · rw [hcountK]
    omega
