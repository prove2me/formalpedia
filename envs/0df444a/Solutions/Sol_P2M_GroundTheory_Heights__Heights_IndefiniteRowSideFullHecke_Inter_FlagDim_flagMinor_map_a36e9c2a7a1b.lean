-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_flagMinor_map_a36e9c2a7a1b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:37:58.282516+00:00
-- url     : https://prove2.me/submissions/26f3f704-34a1-486e-bc55-7b73b9d3061d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagDimSt
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagDim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n N1 : ℕ}
    (M : Matrix (Fin n) (Fin N1) R) (j : Fin (n - 1)) (T : PluckerBlocks N1 n j) :
    flagMinor (M.map f) j T = f (flagMinor M j T) := by
  simp only [flagMinor]
  rw [RingHom.map_det]
  rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
