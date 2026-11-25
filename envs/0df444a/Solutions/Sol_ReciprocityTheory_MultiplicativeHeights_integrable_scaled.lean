-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.integrable_scaled
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:32:06.606811+00:00
-- url     : https://prove2.me/submissions/75e16ef7-0e14-44e6-a3b8-15b03e628b44

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorusA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorusB
import Theorems.Thm_P2M_ReciprocityTheory_MultiplicativeHeights_eval_bind__scale_2138dfaeca51
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights
open MeasureTheory
private theorem bind1_C_mul_X_ne_zero_of_ne_zero {ι : Type} (r : ι → ℂ) (hr : ∀ j, r j ≠ 0)
    (f : MvPolynomial ι ℂ) (hf : f ≠ 0) :
    MvPolynomial.bind₁ (fun j => MvPolynomial.C (r j) * MvPolynomial.X j) f ≠ 0 := by
  intro h
  apply hf
  refine MvPolynomial.funext fun v => ?_
  have hv := eval_bind₁_scale r (fun j => v j / r j) f
  rw [h, map_zero] at hv
  have e : (fun j => r j * (v j / r j)) = v := by
    funext j
    first
      | exact mul_div_cancel₀ (v j) (hr j)
      | field_simp [hr j]
      | (rw [mul_comm]; exact div_mul_cancel₀ (v j) (hr j))
  rw [e] at hv
  rw [← hv, map_zero]
end ReciprocityTheory.MultiplicativeHeights
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {ι : Type} [Fintype ι] (hBasic : TorusMeanBasicStatement)
    (f : MvPolynomial ι ℂ) (hf : f ≠ 0) (r : ι → ℂ) (hr : ∀ j, r j ≠ 0) :
    Integrable (fun θ => Real.log ‖MvPolynomial.eval (fun j => r j * torusPoint θ j) f‖)
      (torusProb ι) := by
  have h := (hBasic ι).1 _ (bind1_C_mul_X_ne_zero_of_ne_zero r hr f hf)
  simpa only [eval_bind₁_scale] using h
end ReciprocityTheory.MultiplicativeHeights
