-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_key_71b309e14059
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:15:12.296285+00:00
-- url     : https://prove2.me/submissions/13183a5a-3e4c-4006-8a32-c84be05577f2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerRel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerRel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_homog_zero_d7e93627f978
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_wedge_mul_delta_7ff44f6dfd11
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_coord_base_7abc0b27051f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_rename_X_base_630ad48861ea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_chart_form_82dccfe371dc

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
open GroundTheory.Heights₂.Heights.Inter.PluckerRelations
variable {D : ℕ} (S : ProjectiveLineBundle D)
namespace GroundTheory.Heights₂.Heights.Inter.PluckerRelations
theorem _root_.solution (i : S.ι) (l : S.ν) (k m : S.κ) :
    ∃ (d : ℕ) (Q : MRing S.YIdx), IsMultiHomog Q (Pi.single T.YBlk.base (d + 4)) ∧
      IsMultiHomog (rename (T.yyEmb 0) Q : MRing S.WIdx) (Pi.single T.WBlk.base (d + 4)) ∧
      aeval (T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1)) (rename (T.yyEmb 0) Q) =
        algebraMap S.Ω S.Φ (S.x i ^ (d + 1) * (wedgeVal S k m * S.δ l)) := by
  by_cases hi : S.x i = 0
  · refine ⟨0, 0, homog_zero _, homog_zero _, ?_⟩
    simp [hi]
  · obtain ⟨a, ha, hpa⟩ := wedge_mul_delta S i hi l k m
    obtain ⟨d, Q, hQ, hQ', hv⟩ := chart_form S i hi ha
    refine ⟨d, Q * X ⟨T.YBlk.base, i⟩ ^ 4, ?_, ?_, ?_⟩
    · convert exHomog_mul hQ (exHomog_pow (exHomog_X (ι := S.YIdx) T.YBlk.base i) 4) using 1
      funext b; cases b <;> simp
    · rw [map_mul, map_pow, rename_X_base]
      convert exHomog_mul hQ' (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.base i) 4) using 1
      funext b; cases b <;> simp
    · rw [map_mul, map_pow, rename_X_base, map_mul, map_pow, aeval_X, hv, coord_base, hpa]
      simp only [map_mul, map_pow]
      ring
end GroundTheory.Heights₂.Heights.Inter.PluckerRelations
