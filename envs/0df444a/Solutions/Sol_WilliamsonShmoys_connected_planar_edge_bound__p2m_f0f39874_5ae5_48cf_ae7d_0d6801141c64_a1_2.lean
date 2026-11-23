-- Prove2me | solution 2 for WilliamsonShmoys.connected_planar_edge_bound__p2m_f0f39874_5ae5_48cf_ae7d_0d6801141c64_a1
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T18:22:01.225794+00:00
-- url     : https://prove2.me/submissions/ae7579ad-9fa3-484b-b693-72f51bf8be31


import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound__p2m_52ae77ae_f85b_40f5_bd03_34373df951b6_a2
-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_f0f39874_5ae5_48cf_ae7d_0d6801141c64_a1
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_f0f39874_5ae5_48cf_ae7d_0d6801141c64_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:44:53.053225+00:00
-- url     : https://prove2.me/theorems/afce1f76-d895-40f4-a39d-a07d8ca5218a
-- title:
--   Edge bound for connected planar graphs
-- statement:
--   A finite connected simple graph with a crossing-free drawing and at least three vertices has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).
open WilliamsonShmoys

theorem _root_.solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  first
    | exact _root_.WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_52ae77ae_f85b_40f5_bd03_34373df951b6_a2
    | (apply _root_.WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_52ae77ae_f85b_40f5_bd03_34373df951b6_a2 <;> assumption)
