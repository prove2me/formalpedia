-- Prove2me | solution 2 for WilliamsonShmoys.connected_planar_edge_upper__p2m_ad7657d2_129c_4ff8_bf1d_16d96be983d7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T13:50:41.493966+00:00
-- url     : https://prove2.me/submissions/b84107fd-6039-47c4-afa7-9bf6de1efaa3


import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound__p2m_52ae77ae_f85b_40f5_bd03_34373df951b6_a2
-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_upper__p2m_ad7657d2_129c_4ff8_bf1d_16d96be983d7_a1
-- name    : WilliamsonShmoys.connected_planar_edge_upper__p2m_ad7657d2_129c_4ff8_bf1d_16d96be983d7_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:42:08.202756+00:00
-- url     : https://prove2.me/theorems/b5c387cc-fe7e-4039-9011-ee95aed75dd4
-- title:
--   Connected simple planar graph edge upper bound
-- statement:
--   A connected simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges. Prove it using Euler’s formula and face-boundary incidences.
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
