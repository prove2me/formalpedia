-- Prove2me | solution 1 for ReciprocityTheory.Cheb.sum_mult_logDev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:45:28.703695+00:00
-- url     : https://prove2.me/submissions/2b999ab1-fc39-455f-88ca-a8c94a8d8015

import Definitions.Def_ReciprocityTheory_Chebotarev_UnitPart
import Definitions.Def_ReciprocityTheory_Chebotarev_Support

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution {x : mixedSpace E} (hx : mixedEmbedding.norm x ≠ 0) :
    ∑ w : InfinitePlace E, (w.mult : ℝ) * (Real.log (normAtPlace w x) -
      Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ E : ℝ)⁻¹) = 0 := by
  have hne := mixedEmbedding.norm_ne_zero_iff.mp hx
  have hlog : Real.log (mixedEmbedding.norm x) =
      ∑ w : InfinitePlace E, (w.mult : ℝ) * Real.log (normAtPlace w x) := by
    rw [mixedEmbedding.norm_apply, Real.log_prod (fun w _ => pow_ne_zero _ (hne w))]
    simp [Real.log_pow]
  have hd : (Module.finrank ℚ E : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := E)).ne'
  have hm : (∑ w : InfinitePlace E, (w.mult : ℝ)) = Module.finrank ℚ E := by
    exact_mod_cast InfinitePlace.sum_mult_eq
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [← hlog, ← Finset.sum_mul, hm]
  field_simp
  ring
end ReciprocityTheory.Cheb
