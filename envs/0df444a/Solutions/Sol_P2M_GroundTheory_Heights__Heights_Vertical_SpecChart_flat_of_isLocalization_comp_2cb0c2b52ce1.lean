-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_flat_of_isLocalization_comp_2cb0c2b52ce1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:23:28.284641+00:00
-- url     : https://prove2.me/submissions/e46c1603-745e-4c22-9ce3-bdb8dbb9612b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartQuot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.SpecChart
variable {A : Type*} [CommRing A] (W : Ideal A) [W.IsPrime] (P : Ideal A)
namespace GroundTheory.Heights₂.Heights.Vertical.SpecChart
theorem _root_.solution {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (g : S →+* T) (hg : (g.comp (algebraMap R S)).Flat) :
    g.Flat := by
  letI := g.toAlgebra
  letI : Algebra R T := (g.comp (algebraMap R S)).toAlgebra
  haveI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (Module.flat_iff_of_isLocalization S M T).mpr hg
end GroundTheory.Heights₂.Heights.Vertical.SpecChart
