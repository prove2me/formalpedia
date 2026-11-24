-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjectivePointsOfPlane_map_eval__int_3dc61e60a001
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:56:59.070699+00:00
-- url     : https://prove2.me/submissions/60d99dca-8a61-4960-9cde-7c44af86ffad

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ProjProjApply
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjPtsOfPlane

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.ProjectivePointsOfPlane
namespace GroundTheory.Heights₂.Heights.ProjectivePointsOfPlane
theorem _root_.solution {ι A B : Type*} [CommRing A] [CommRing B] (k : A →+* B) (c : ℤ →+* A) (g : ι → A)
    (f : MvPolynomial ι ℤ) :
    k (eval₂ c g f) = eval₂ (Int.castRingHom B) (k ∘ g) f := by
  rw [eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _
end GroundTheory.Heights₂.Heights.ProjectivePointsOfPlane
