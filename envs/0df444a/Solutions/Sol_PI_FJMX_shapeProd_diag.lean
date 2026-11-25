-- Prove2me | solution 1 for PI.FJMX.shapeProd_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:52:57.019682+00:00
-- url     : https://prove2.me/submissions/7ffa202b-3b3a-4cf5-ac97-83fac77ddf18

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurElim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistWt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LeadTDerCols
import Theorems.Thm_PI_FJMX_leadT_diag
import Theorems.Thm_PI_FJMX_shape_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FJMX
variable {σ : Type*} {m : ℕ}
namespace PI.FJMX
theorem _root_.solution (ι : Fin m × Fin m → σ) (hι : Function.Injective ι) (α : Fin m → ℕ) (hα : Antitone α) :
    aeval (PI.FJMB.killS (PI.FJMB.offD ι)) (PI.FJM.shapeProd (blkM ι) (List.ofFn α)) =
      ∏ i, X (ι (i, i)) ^ α i := by
  classical
  have hpw : (List.ofFn α).Pairwise (· ≥ ·) := by
    rw [List.pairwise_ofFn]
    intro i j hij
    exact hα hij.le
  unfold PI.FJM.shapeProd
  rw [map_prod]
  have e1 : ∀ t ∈ Finset.range (List.ofFn α).length,
      aeval (PI.FJMB.killS (PI.FJMB.offD ι)) (PI.FJM.leadT (blkM ι) (t + 1) ^
        ((List.ofFn α).getD t 0 - (List.ofFn α).getD (t + 1) 0)) =
      ∏ i : Fin m, X (ι (i, i)) ^ ((if i.val < t + 1 then 1 else 0) *
        ((List.ofFn α).getD t 0 - (List.ofFn α).getD (t + 1) 0)) := by
    intro t ht
    simp only [List.length_ofFn, Finset.mem_range] at ht
    rw [map_pow, leadT_diag ι hι (t + 1) (by omega), ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    rw [pow_mul]
  rw [Finset.prod_congr rfl e1, Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  simp only [List.length_ofFn]
  have := shape_sum (List.ofFn α) hpw i.val
  rw [List.length_ofFn] at this
  simp only [smul_eq_mul] at this
  rw [show (∑ t ∈ Finset.range m, (if i.val < t + 1 then 1 else 0) *
      ((List.ofFn α).getD t 0 - (List.ofFn α).getD (t + 1) 0)) =
      ∑ t ∈ Finset.range m, ((List.ofFn α).getD t 0 - (List.ofFn α).getD (t + 1) 0) *
        (if i.val < t + 1 then 1 else 0) from Finset.sum_congr rfl (fun _ _ => mul_comm _ _), this]
  simp
end PI.FJMX
