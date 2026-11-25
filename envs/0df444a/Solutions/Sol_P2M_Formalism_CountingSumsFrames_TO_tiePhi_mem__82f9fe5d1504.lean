-- Prove2me | solution 1 for P2M_Formalism_CountingSumsFrames_TO_tiePhi_mem__82f9fe5d1504
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:32:43.263704+00:00
-- url     : https://prove2.me/submissions/f3ad3ddd-3201-4517-a1ec-c134645ad594

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_pow_mem
import Theorems.Thm_Formalism_GM_FockB_X_mem
import Theorems.Thm_Formalism_GM_FockB_mulLeft_mem
import Theorems.Thm_Formalism_GM_FockB_pderiv_mem


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
variable {k σ : Type} [Field k]
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution {r : ℕ} (w e : Fin r → σ) (o n z : ℕ) :
    (Formalism.GM.tiePhi w e o n z : Module.End k (MvPolynomial σ k)) ∈ FockB.Ops (Set.range w ∪ Set.range e) := by
  unfold Formalism.GM.tiePhi
  refine sum_mem fun j _ => Subalgebra.smul_mem _ ?_ _
  rw [← Module.End.mul_eq_comp]
  refine mul_mem (pow_mem ?_ _) (pow_mem ?_ _)
  · exact FockB.mulLeft_mem (sum_mem fun c _ => mul_mem (FockB.X_mem (Or.inl ⟨c, rfl⟩))
      (FockB.X_mem (Or.inr ⟨c, rfl⟩)))
  · unfold Formalism.GM.tieF
    refine sum_mem fun c _ => ?_
    rw [← Module.End.mul_eq_comp]
    exact mul_mem (FockB.pderiv_mem (Or.inl ⟨c, rfl⟩)) (FockB.pderiv_mem (Or.inr ⟨c, rfl⟩))
end Formalism.CountingSumsFrames.TO
