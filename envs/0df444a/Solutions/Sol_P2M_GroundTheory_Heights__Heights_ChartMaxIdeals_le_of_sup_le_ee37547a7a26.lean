-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_le_of_sup_le_ee37547a7a26
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:51:34.423138+00:00
-- url     : https://prove2.me/submissions/a2f5b961-ad8b-4318-a217-91c3c84a2112

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProperSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartMaxIdeals

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartMaxIdeals
variable {F : Type} [Field F] {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartMaxIdeals
theorem _root_.solution (hD : ChartDehomog.Statement) {W₁ W₂ : Ideal (MvPolynomial (Fin n) F)} {t : Fin n → F}
    (hh₁ : IsHomogIdeal W₁) (h₂ : W₂.IsPrime) (hh₂ : IsHomogIdeal W₂) (ht₂ : linForm t ∉ W₂)
    (h : W₁ ⊔ Ideal.span {linForm t - 1} ≤ W₂ ⊔ Ideal.span {linForm t - 1}) : W₁ ≤ W₂ := by
  intro g hg
  rw [← sum_homogeneousComponent g]
  refine Ideal.sum_mem _ fun d _ => ?_
  exact hD F n W₂ t _ d h₂ hh₂ ht₂ (homogeneousComponent_isHomogeneous d g)
    (h (Ideal.mem_sup_left (hh₁ g hg d)))
end GroundTheory.Heights₂.Heights.ChartMaxIdeals
