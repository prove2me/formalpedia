-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjectivePointsOfPlane_map_aeval_int_01a6887550a7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:47:51.556362+00:00
-- url     : https://prove2.me/submissions/c96f6326-9a60-418f-9341-a170a8127a8b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ProjProjApply
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjPtsOfPlane
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectivePointsOfPlane_map_eval__int_3dc61e60a001

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
theorem _root_.solution {ι A B : Type*} [CommRing A] {_ : Algebra ℤ A} [CommRing B] (k : A →+* B) (g : ι → A)
    (f : MvPolynomial ι ℤ) :
    k (aeval g f) = eval₂ (Int.castRingHom B) (k ∘ g) f := by
  rw [aeval_def, map_eval₂_int]
end GroundTheory.Heights₂.Heights.ProjectivePointsOfPlane
