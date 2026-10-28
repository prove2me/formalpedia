-- Prove2me | solution 1 for WilliamsonShmoys.triangulation_euler_data_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T06:09:34.573994+00:00
-- url     : https://prove2.me/submissions/6fa48fa2-5db4-4172-9de8-40fba2e00fbf

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarTriangulationEulerData

set_option autoImplicit false

theorem side_count_aux
    {V : Type} [Fintype V] [DecidableEq V] (K : SimpleGraph V)
    (data : WilliamsonShmoys.TriangulatedSphereFaceData K) :
    3 * (@Fintype.card data.Face data.faceFintype : Int) = 2 * (K.edgeSet.ncard : Int) := by
  classical
  letI := data.faceFintype
  letI := data.faceDecidableEq
  let f : data.Face × Fin 3 → Sym2 V := fun s =>
    Sym2.mk (data.boundary s.1 s.2) (data.boundary s.1 (s.2 + 1))
  have hmaps : ∀ s ∈ (Finset.univ : Finset (data.Face × Fin 3)), f s ∈ K.edgeFinset := by
    intro s _
    rw [SimpleGraph.mem_edgeFinset]
    exact data.side_adjacent s.1 s.2
  have h := Finset.card_eq_sum_card_fiberwise hmaps
  have h2 : ∀ e ∈ K.edgeFinset,
      ((Finset.univ : Finset (data.Face × Fin 3)).filter (fun a => f a = e)).card = 2 := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he
    have := data.edge_incidence e he
    convert this
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin] at h
  have h3 : K.edgeSet.ncard = K.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  rw [h3]
  have : Fintype.card data.Face * 3 = K.edgeFinset.card * 2 := h
  omega

theorem solution
    {V : Type} [Fintype V] [DecidableEq V] (K : SimpleGraph V)
    (data : WilliamsonShmoys.TriangulatedSphereFaceData K) :
    (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  have h := side_count_aux K data
  have e := data.euler
  omega
