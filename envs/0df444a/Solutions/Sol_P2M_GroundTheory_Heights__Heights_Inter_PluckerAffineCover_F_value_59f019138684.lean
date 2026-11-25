-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_F_value_59f019138684
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:14:22.454258+00:00
-- url     : https://prove2.me/submissions/89c18159-25e5-4398-8a12-6089f3f5099b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerCover
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_aeval_of_mem_ker_c4e20c757a43
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_wwCoord_comp_1b68d214eb86
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_not_mem_ker_iff_aeval_ne_69965e549228


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
variable {D : ℕ} (S : ProjectiveLineBundle D)
namespace GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
theorem _root_.solution (N : ℕ) (F : S.ι → S.ν → S.κ → S.κ → MRing S.YIdx) (hF : S.IsPluckerRel N F)
    (i : S.ι) (l : S.ν) (k m : S.κ) :
    aeval (yyc S) (F i l k m) = algebraMap S.Ω S.Φ
      ((S.φ k (S.e 0) * S.φ m (S.e 1) - S.φ k (S.e 1) * S.φ m (S.e 0)) * S.δ l * S.x i ^ N) := by
  have h0 := aeval_of_mem_ker _ (hF.2 i l k m)
  have hh : aeval (T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1)) S.h ≠ 0 :=
    (DiagRAux.not_mem_ker_iff_aeval_ne _ S.h _ S.h_deg).1 S.h_nmem
  have ha : S.a 1 - S.a 0 ≠ 0 := sub_ne_zero.2 fun h => absurd (S.indep.injective h) (by decide)
  have hren : aeval (T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1)) (rename (T.yyEmb 0) (F i l k m)) =
      aeval (yyc S) (F i l k m) := by
    rw [aeval_rename, wwCoord_comp]
  have hg := S.quot
  rw [map_sub, map_mul, map_mul, map_mul, map_mul, map_pow, hren, hg, aeval_X, aeval_X] at h0
  simp only [ProjectiveLineBundle.pluckerWW, map_sub, map_mul, aeval_X, T.wwCoord, T.lineVal, T.diagSec] at h0
  apply mul_left_cancel₀ (mul_ne_zero ha hh)
  simp only [map_mul, map_sub, map_pow]
  linear_combination h0
end GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
