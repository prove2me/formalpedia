-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_CurveDegreeVert_logNorm_sameOrbit_6d28cae3f9e4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:21:04.309576+00:00
-- url     : https://prove2.me/submissions/b0d7af0e-3c7c-428f-adff-b57bf2008320

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveDegreeVert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsIsSheetFinZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveDegreeVert
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_eval_smul_homog


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GroundTheory.Heights₂.Heights.Inter
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.CurveDegreeVert
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Targets.CurveDegreeVert
theorem _root_.solution {A : HermLine ι} {s : MRing ι} {a : K → ℕ} (ha : ∀ k, A.a k = a k)
    (hs : IsMultiHomog s a) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    logNorm A s z = logNorm A s z' := by
  obtain ⟨c, hc, rfl⟩ := h
  unfold logNorm
  have hn : ∏ k, ‖c k‖ ^ A.a k = ‖∏ k, c k ^ a k‖ := by
    simp [ha, norm_prod, norm_pow]
  have h0 : ‖∏ k, c k ^ a k‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k))
  rw [eval_smul_homog s a hs c z', A.smul c z' hc, norm_mul, hn, mul_div_mul_left _ _ h0]
end GroundTheory.Heights₂.Heights.Targets.CurveDegreeVert
