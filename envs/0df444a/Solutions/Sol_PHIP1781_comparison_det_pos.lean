-- Prove2me | solution 1 for PHIP1781.comparison_det_pos
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T03:34:50.999929+00:00
-- url     : https://prove2.me/submissions/8f41e287-9b3d-4a9d-9b0e-5b99dc5c281b

import Mathlib
open Filter Topology

theorem solution : 0 < Matrix.det (!![1, -(1/10); -(1/10), 2/5] : Matrix (Fin 2) (Fin 2) ℚ) := by
  norm_num [Matrix.det_fin_two]
