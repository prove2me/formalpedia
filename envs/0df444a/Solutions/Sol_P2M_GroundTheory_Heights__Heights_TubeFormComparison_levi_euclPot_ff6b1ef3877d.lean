-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TubeFormComparison_levi_euclPot_ff6b1ef3877d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:35:51.538489+00:00
-- url     : https://prove2.me/submissions/f5901354-9105-4f24-afba-93c88ce2d068

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LogIntegrableOnOfLogIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeFormCompare
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeFormComparison_levi_eq_re_bde4222f82b2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeFormComparison_hessC_euclPot_8b94f23095e1

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
open MvPolynomial Matrix Filter Topology ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.TubeFormComparison
namespace GroundTheory.Heights₂.Heights.TubeFormComparison
theorem _root_.solution {N : ℕ} (z w : Fin N → ℂ) : levi euclPot z w = ∑ j, ‖w j‖ ^ 2 := by
  rw [levi_eq_re, hessC_euclPot, Matrix.one_mulVec]
  simp [dotProduct, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]
end GroundTheory.Heights₂.Heights.TubeFormComparison
