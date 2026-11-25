-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_P1_dehom_monomial_9b7f944b9b7a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:18:26.56087+00:00
-- url     : https://prove2.me/submissions/f935ef56-c384-4c4c-858e-addfe7658f06

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_FderivFderivLogRho
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_FirstPointNeSecondPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_P1_monomial_eq_3a870ea8517f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.P1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.P1
theorem _root_.solution (i j : ℕ) (c : ℤ) :
    dehom (monomial (Finsupp.single p1 i + Finsupp.single p0 j) c) = Polynomial.C c * Polynomial.X ^ i := by
  rw [monomial_eq, map_mul, map_mul, map_pow, map_pow]
  simp only [dehom, coe_eval₂Hom, eval₂_C, eval₂_X, val, p0, p1]
  simp
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.P1
