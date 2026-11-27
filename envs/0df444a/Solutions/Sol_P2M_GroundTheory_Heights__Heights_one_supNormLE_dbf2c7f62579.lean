-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_one_supNormLE_dbf2c7f62579
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:12:15.718146+00:00
-- url     : https://prove2.me/submissions/dd9b88a5-b90f-4c04-ad3e-08a24a68f198

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_chartMonomial_fd0871b69c38


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
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (n : ι → ℕ) (k₀ : ι)
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution :
    ((IntegralSection.one (ArithVariety.whole n)).cast (standard_quot_deg n)).SupNormLE
      (((HermLine.standard n).pow 1).mul (HermLine.standard n).inv) 0 := by
  intro z hz c' d' e he hc'
  have he' : e = chartMonomial c' d' := by
    have h := (Submodule.mem_bot _).mp he.2
    change 1 * e - 1 * chartMonomial c' d' = 0 at h
    linear_combination h
  have hne : evalCone z (chartMonomial c' d') ≠ 0 := by
    rw [evalCone_chartMonomial]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc' k)
  have hpos : 0 < (HermLine.standard n).metric z := (HermLine.standard n).metric_pos z hz.1
  have hm : (((HermLine.standard n).pow 1).mul (HermLine.standard n).inv).metric z = 1 := by
    change (HermLine.standard n).metric z ^ 1 * ((HermLine.standard n).metric z)⁻¹ = 1
    rw [pow_one, mul_inv_cancel₀ hpos.ne']
  rw [he', hm, mul_one, div_self (norm_ne_zero_iff.mpr hne), Real.exp_zero]
end GroundTheory.Heights₂.Heights
