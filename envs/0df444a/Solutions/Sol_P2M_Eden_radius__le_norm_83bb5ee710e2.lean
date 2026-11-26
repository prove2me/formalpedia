-- Prove2me | solution 1 for P2M_Eden_radius__le_norm_83bb5ee710e2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:38:50.124915+00:00
-- url     : https://prove2.me/submissions/9c22faa2-12b8-4728-80a6-9ab1e3616051

import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_AttractorDistance
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_UniformAttraction
import Theorems.Thm_Eden_norm_sq_phaseSpace
import Theorems.Thm_P2M_Eden_radiusSq__nonneg_5272e4fb8458
import Theorems.Thm_P2M_Eden_radiusSq__nonneg_7729c3bfdb8d


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution (p : PhaseSpace) : Real.sqrt (radiusSq₁ p) ≤ ‖p‖ := by
  have hn := norm_sq_phaseSpace p
  have hs := Real.sq_sqrt (radiusSq₁_nonneg p)
  nlinarith [radiusSq₂_nonneg p, sq_nonneg (p 4), norm_nonneg p, Real.sqrt_nonneg (radiusSq₁ p)]
end Eden
