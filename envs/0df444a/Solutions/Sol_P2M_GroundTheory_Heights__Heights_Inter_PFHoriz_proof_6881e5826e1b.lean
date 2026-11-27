-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PFHoriz_proof_6881e5826e1b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:02:16.173937+00:00
-- url     : https://prove2.me/submissions/442c1cf0-5cb7-4eec-a29b-08bfd5f0876d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFHoriz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFHoriz
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PFHoriz_fibreIdeal_genFibreOf_3eecdf1a8d31

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
namespace PFHoriz
theorem _root_.solution : PFHoriz.Statement := by
  intro I r hPF K _ ι _ K' _ ι' _ κ v P' W d G J L L' N hκv hW hWP hP hJ hL hLL hN
  haveI : W.IsPrime := hW.2.1.1
  have h := hPF K ι K' ι' κ v W d (PFHoriz.genFibreOf G W hWP) J L L' N hκv hW (by rw [hWP]; exact hP)
    hJ hL hLL hN
  rw [PFHoriz.fibreIdeal_genFibreOf hWP hκv G, hWP] at h
  exact h
end PFHoriz
end GroundTheory.Heights₂.Heights.Inter
