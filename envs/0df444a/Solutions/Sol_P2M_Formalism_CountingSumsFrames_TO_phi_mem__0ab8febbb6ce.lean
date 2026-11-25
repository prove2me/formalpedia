-- Prove2me | solution 1 for P2M_Formalism_CountingSumsFrames_TO_phi_mem__0ab8febbb6ce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:43:43.103835+00:00
-- url     : https://prove2.me/submissions/8e5eec0c-5633-4f0f-b64e-0ba518d10b69

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_P2M_Formalism_CountingSumsFrames_TO_tiePhi_mem__82f9fe5d1504
import Theorems.Thm_Formalism_GM_FockB_ops_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution (L : Letters N) (T : TieData) (j : Fin T.t) (h : T.pos j + 1 < N) :
    (T.phi p L j : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈
      FockB.Ops {v : Fin N × Fin r | (v.1 : ℕ) = T.pos j ∨ (v.1 : ℕ) = T.pos j + 1} := by
  unfold TieData.phi
  rw [dif_pos h]
  unfold tiePhiAt
  refine FockB.ops_mono ?_ (tiePhi_mem' _ _ _ _ _)
  rintro v (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · left; rfl
  · right; rfl
end Formalism.CountingSumsFrames.TO
