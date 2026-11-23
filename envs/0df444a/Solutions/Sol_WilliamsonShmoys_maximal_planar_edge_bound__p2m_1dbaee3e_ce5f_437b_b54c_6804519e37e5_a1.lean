-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound__p2m_1dbaee3e_ce5f_437b_b54c_6804519e37e5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T19:08:34.928232+00:00
-- url     : https://prove2.me/submissions/65513130-4790-4794-b48c-62b4f0a4f279


import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_b05b2ac9_cf86_42cd_81eb_d15df4254060_a2
-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_1dbaee3e_ce5f_437b_b54c_6804519e37e5_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_bound__p2m_1dbaee3e_ce5f_437b_b54c_6804519e37e5_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T08:18:19.515735+00:00
-- url     : https://prove2.me/theorems/f01ce2e1-140e-4537-aebf-61aea436c359
-- title:
--   Edge bound for maximal planar graphs
-- statement:
--   A finite simple graph on at least three vertices that has a crossing-free drawing and is maximal among planar supergraphs on the same vertex type has at most 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).
open WilliamsonShmoys

set_option autoImplicit false

theorem _root_.solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hMaximal : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
      K.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  first
    | exact _root_.WilliamsonShmoys.maximal_planar_edge_bound__p2m_b05b2ac9_cf86_42cd_81eb_d15df4254060_a2
    | (apply _root_.WilliamsonShmoys.maximal_planar_edge_bound__p2m_b05b2ac9_cf86_42cd_81eb_d15df4254060_a2 <;> assumption)
