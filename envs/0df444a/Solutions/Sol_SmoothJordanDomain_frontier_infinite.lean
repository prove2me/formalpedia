-- Prove2me | solution 1 for SmoothJordanDomain.frontier_infinite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:12:19.083806+00:00
-- url     : https://prove2.me/submissions/07bbd81a-5905-40ea-a934-aa92c821e5a7

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction

set_option autoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u
namespace SmoothJordanDomain
theorem _root_.solution (Omega : SmoothJordanDomain) :
    (frontier Omega.carrier).Infinite := by
  rw [← Omega.boundaryParam_range]
  have himage :
      (Omega.boundaryParam '' Ico (0 : ℝ) (2 * Real.pi)).Infinite :=
    (Ico_infinite Real.two_pi_pos).image Omega.boundaryParam_injOn
  exact himage.mono (image_subset_range _ _)
end SmoothJordanDomain
