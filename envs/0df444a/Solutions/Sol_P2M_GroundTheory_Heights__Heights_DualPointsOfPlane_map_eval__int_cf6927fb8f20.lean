-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualPointsOfPlane_map_eval__int_cf6927fb8f20
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:25.907954+00:00
-- url     : https://prove2.me/submissions/a8ae7341-fde8-42d7-8c9d-644d43252f78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualProjApply
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPtsOfPlane

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
theorem _root_.solution {ι A B : Type*} [CommRing A] [CommRing B] (k : A →+* B) (c : ℤ →+* A) (g : ι → A)
    (f : MvPolynomial ι ℤ) :
    k (eval₂ c g f) = eval₂ (Int.castRingHom B) (k ∘ g) f := by
  rw [eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _
end GroundTheory.Heights₂.Heights.DualPointsOfPlane
