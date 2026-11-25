-- Prove2me | solution 1 for PositivityTheory.CW.FormEigenMonotone.norm_fib
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:26:18.926258+00:00
-- url     : https://prove2.me/submissions/32be7f89-4e62-43cc-91e2-cfa4bb0147ec

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_BasisSumOfOrthogonality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.FormEigenMonotone
variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V} {ι : Type} {b : Module.Basis ι ℂ V} {μ : ι → ℝ}
namespace PositivityTheory.CW.FormEigenMonotone
theorem _root_.solution (hb : Orthonormal ℂ b) (f : V →ₗ[ℂ] ℂ) (F : Finset ι) :
    ‖∑ j ∈ F, starRingEnd ℂ (f (b j)) • b j‖ ^ 2 = ∑ j ∈ F, ‖f (b j)‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ, hb.inner_sum, RCLike.re_to_complex, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.conj_conj, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
end PositivityTheory.CW.FormEigenMonotone
