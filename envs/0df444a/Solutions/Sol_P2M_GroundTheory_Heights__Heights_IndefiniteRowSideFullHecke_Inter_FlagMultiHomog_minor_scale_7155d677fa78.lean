-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_minor_scale_7155d677fa78
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:42:11.496309+00:00
-- url     : https://prove2.me/submissions/da8810fb-cb0f-4f92-8a50-a58b64dfb613

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveComplexPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagMultiHomog
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_map_flagMinor_f33e98c804ee
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_flagMinor_diagonal_mul_33770a16194e

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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMultiHomog
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] {n N1 : ℕ} (θ j0 : R →+* S)
    (G : Matrix (Fin n) (Fin n) R) (Bc : Matrix (Fin n) (Fin N1) R) (d : Fin n → S)
    (h : Matrix (Fin n) (Fin n) S) (Bs : Matrix (Fin n) (Fin N1) S)
    (hG : G.map θ = Matrix.diagonal d * G.map j0 * h) (hBs : Bc.map θ = Bs) (hh : h * Bs = Bc.map j0)
    (j : Fin (n - 1)) (T : PluckerBlocks N1 n j) :
    θ (flagMinor (G * Bc) j T) =
      (∏ a : Fin (j.1 + 1), d ⟨a.1, by have := j.2; omega⟩) * j0 (flagMinor (G * Bc) j T) := by
  rw [map_flagMinor, map_flagMinor, Matrix.map_mul, Matrix.map_mul, hG, hBs,
    Matrix.mul_assoc (Matrix.diagonal d * G.map j0), hh, Matrix.mul_assoc, flagMinor_diagonal_mul]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMultiHomog
