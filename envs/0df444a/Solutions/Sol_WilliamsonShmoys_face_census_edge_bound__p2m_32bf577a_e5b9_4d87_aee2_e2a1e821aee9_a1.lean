-- Prove2me | solution 1 for WilliamsonShmoys.face_census_edge_bound__p2m_32bf577a_e5b9_4d87_aee2_e2a1e821aee9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:18:37.804163+00:00
-- url     : https://prove2.me/submissions/b6d20a5a-4f68-47b4-ba9f-7fe4364b2e69

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open scoped BigOperators

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj) (F : ℕ)
    (boundary : Fin F → ℕ)
    (hEuler : Fintype.card V + F = K.edgeFinset.card + 2)
    (hDouble : (∑ f : Fin F, boundary f) = 2 * K.edgeFinset.card)
    (hFaces : ∀ f : Fin F, 3 ≤ boundary f) :
    K.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  have hsum : (∑ f : Fin F, (3 : ℕ)) ≤ ∑ f : Fin F, boundary f :=
    Finset.sum_le_sum fun f _ => hFaces f
  have hconst : (∑ f : Fin F, (3 : ℕ)) = F * 3 := by simp
  rw [hconst, hDouble] at hsum
  omega