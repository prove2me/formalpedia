-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_eval_one_scaleHom_ff58bea7d832
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:26:32.491979+00:00
-- url     : https://prove2.me/submissions/852db7bd-4f83-43f8-9424-f39bb4d2d355

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveComplexPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagMultiHomog

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMultiHomog
variable {L : Type} [DecidableEq L] {κ : L → Type} {R : Type} [CommRing R]
omit [DecidableEq L]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMultiHomog
theorem _root_.solution (φ : MvPolynomial (Σ b, κ b) ℤ →+* R) (f : MvPolynomial (Σ b, κ b) ℤ) :
    eval (fun _ => 1) (scaleHom (L := L) φ f) = φ f := by
  have h : (eval fun _ : L => (1 : R)).comp (scaleHom φ) = φ :=
    MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun q => by simp [scaleHom]
  exact RingHom.congr_fun h f
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMultiHomog
