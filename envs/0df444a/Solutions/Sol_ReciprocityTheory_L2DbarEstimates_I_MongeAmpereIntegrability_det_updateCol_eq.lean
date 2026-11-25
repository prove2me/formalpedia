-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.det_updateCol_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:30:04.89312+00:00
-- url     : https://prove2.me/submissions/b9cb7d55-4f06-44a9-b8f2-e8356bbffe20

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IntegralFderivApplyEqZero
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_DetUpdateColEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability
open MeasureTheory Filter Topology Set
open scoped ContDiff
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability
theorem _root_.solution (M : Matrix (Fin n) (Fin n) ℂ) (k : Fin n) (b : Fin n → ℂ) :
    (M.updateCol k b).det = ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * (b (σ k) * ∏ l ∈ Finset.univ.erase k, M (σ l) l) := by
  rw [Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k),
    Matrix.updateCol_self]
  congr 2
  exact Finset.prod_congr rfl fun l hl => Matrix.updateCol_ne (Finset.ne_of_mem_erase hl)
end ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability
