-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualPointsOfPlane_map_aeval_int_f4689206ea1e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:22:33.356627+00:00
-- url     : https://prove2.me/submissions/acfdff10-52c5-4845-8836-1eb05ce7016d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualProjApply
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPtsOfPlane
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualPointsOfPlane_map_eval__int_cf6927fb8f20

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
open GroundTheory.Heights₂.Heights.DualPointsOfPlane
namespace GroundTheory.Heights₂.Heights.DualPointsOfPlane
theorem _root_.solution {ι A B : Type*} [CommRing A] {_ : Algebra ℤ A} [CommRing B] (k : A →+* B) (g : ι → A)
    (f : MvPolynomial ι ℤ) :
    k (aeval g f) = eval₂ (Int.castRingHom B) (k ∘ g) f := by
  rw [aeval_def, map_eval₂_int]
end GroundTheory.Heights₂.Heights.DualPointsOfPlane
