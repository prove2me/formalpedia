-- Prove2me | solution 1 for P2M_Eden_radius__le_norm_a59aead72dbe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:39:00.714343+00:00
-- url     : https://prove2.me/submissions/dd4ef4ab-da23-4012-be9e-b65c9b41e39c

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
theorem _root_.solution (p : PhaseSpace) : Real.sqrt (radiusSq₂ p) ≤ ‖p‖ := by
  have hn := norm_sq_phaseSpace p
  have hs := Real.sq_sqrt (radiusSq₂_nonneg p)
  nlinarith [radiusSq₁_nonneg p, sq_nonneg (p 4), norm_nonneg p, Real.sqrt_nonneg (radiusSq₂ p)]
end Eden
