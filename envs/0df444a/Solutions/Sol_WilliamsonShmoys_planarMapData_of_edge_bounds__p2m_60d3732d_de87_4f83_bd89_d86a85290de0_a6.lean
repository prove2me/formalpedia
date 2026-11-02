-- Prove2me | solution 1 for WilliamsonShmoys.planarMapData_of_edge_bounds__p2m_60d3732d_de87_4f83_bd89_d86a85290de0_a6
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:45:06.379369+00:00
-- url     : https://prove2.me/submissions/58e550b0-6c66-4caf-921b-cffed3520dd0

import Definitions.Def_PlanarMapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3
import Mathlib

theorem solution
    {V : Type} [Fintype V]
    (J : SimpleGraph V) [DecidableRel J.Adj]
    (hcard : 3 <= Fintype.card V)
    (hlow : Fintype.card V <= J.edgeFinset.card + 1)
    (hupp : J.edgeFinset.card + 6 <= 3 * Fintype.card V) :
    Nonempty (PlanarMapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3 J) := by
  classical
  let n : Nat := Fintype.card V
  let E : Nat := J.edgeFinset.card
  let F : Nat := E + 2 - n
  have hlow' : n <= E + 1 := by exact hlow
  have hupp' : E + 6 <= 3 * n := by exact hupp
  have hEuler : n + F = E + 2 := by
    dsimp [F]
    omega
  have hFpos : 0 < F := by
    dsimp [F]
    omega
  have hsurplus : 3 * F <= 2 * E := by
    dsimp [F]
    omega
  let f0 : Fin F := Fin.mk 0 hFpos
  refine Nonempty.intro {
    faceCount := F
    euler := by simpa [n, E] using hEuler
    faceDegree := fun i => 3 + if i = f0 then 2 * E - 3 * F else 0
    sum_faceDegree := by
      simp [Finset.sum_add_distrib, f0] <;> omega
    faceDegree_ge_three := by
      intro i
      split <;> omega
  }