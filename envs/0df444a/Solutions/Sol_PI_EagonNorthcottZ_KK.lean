-- Prove2me | solution 1 for PI.EagonNorthcottZ.KK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:19:11.732459+00:00
-- url     : https://prove2.me/submissions/87221a8f-d0cc-4d52-98f2-c981ad9ac273

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_YHom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_ExactSecondDegreeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_DivisionPartitionTotal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_AugmentationDegreeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EagonNorthcottZ
open MvPolynomial Finset
namespace PI.EagonNorthcottZ
theorem _root_.solution {D : ℕ} (t u : Fin D → P D) (ω : W D) (J : Finset (Fin D)) :
    K t (K u ω) J = ∑ i ∈ Jᶜ, ∑ l ∈ Jᶜ, (if l = i then 0 else
      (sgn i J : P D) * (sgn l (insert i J) : P D) * (t i * u l) * ω (insert l (insert i J))) := by
  simp only [K]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, Finset.compl_insert, ← Finset.filter_ne', Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro l _
  by_cases h : l = i
  · simp [h]
  · simp only [h, if_false, ne_eq, not_false_eq_true, if_true]
    ring
end PI.EagonNorthcottZ
