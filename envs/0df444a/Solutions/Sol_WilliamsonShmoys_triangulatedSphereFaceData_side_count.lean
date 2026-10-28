-- Prove2me | solution 1 for WilliamsonShmoys.triangulatedSphereFaceData_side_count
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T06:08:58.636205+00:00
-- url     : https://prove2.me/submissions/bf57a10f-1374-4f79-b289-a1b6332be17f

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
    (data : WilliamsonShmoys.TriangulatedSphereFaceData K)
    [Fintype data.Face] :
    3 * (Fintype.card data.Face : Int) = 2 * (K.edgeSet.ncard : Int) := by
  have h := side_count_aux K data
  rw [@Fintype.card_eq_nat_card _ data.faceFintype] at h
  rw [Fintype.card_eq_nat_card]; exact h
