-- Prove2me | solution 1 for PHIP1781.comparison_det
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T03:34:43.848355+00:00
-- url     : https://prove2.me/submissions/b3d8d164-14d2-4546-9414-00bc887969df

import Mathlib
open Filter Topology

theorem solution : Matrix.det (!![1, -(1/10); -(1/10), 2/5] : Matrix (Fin 2) (Fin 2) ℚ) = 39/100 := by
  norm_num [Matrix.det_fin_two]
