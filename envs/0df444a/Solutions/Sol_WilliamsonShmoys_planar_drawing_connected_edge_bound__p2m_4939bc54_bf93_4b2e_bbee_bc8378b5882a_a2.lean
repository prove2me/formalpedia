-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_edge_bound__p2m_4939bc54_bf93_4b2e_bbee_bc8378b5882a_a2
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T18:25:35.441695+00:00
-- url     : https://prove2.me/submissions/5257d3bf-6ba8-476b-b611-54c108342c51


import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_simple_planar_drawing_edge_bound__p2m_ae9acfb5_6e8a_4024_8144_fc4b457004a2_a3
-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_edge_bound__p2m_4939bc54_bf93_4b2e_bbee_bc8378b5882a_a2
-- name    : WilliamsonShmoys.planar_drawing_connected_edge_bound__p2m_4939bc54_bf93_4b2e_bbee_bc8378b5882a_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:18:14.552233+00:00
-- url     : https://prove2.me/theorems/c6cbf908-6392-4ad2-b3e3-e51d2dab4847
-- title:
--   Simple edge bound for a connected planar drawing
-- statement:
--   A connected simple graph with at least three vertices and a crossing-free drawing has at most three times its vertex count minus six edges. A proof route is to augment the drawing to a triangulation, derive the face-degree inequality, and combine it with Euler’s formula. This removes the edge-count conclusion from the parent reduction; establishing the augmentation, Euler relation, and face-degree facts for the given drawing definition remains the core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).
open WilliamsonShmoys

theorem _root_.solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  first
    | exact _root_.WilliamsonShmoys.simple_planar_drawing_edge_bound__p2m_ae9acfb5_6e8a_4024_8144_fc4b457004a2_a3
    | (apply _root_.WilliamsonShmoys.simple_planar_drawing_edge_bound__p2m_ae9acfb5_6e8a_4024_8144_fc4b457004a2_a3 <;> assumption)
