-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PackingSeparation.sep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:06:49.186912+00:00
-- url     : https://prove2.me/submissions/06b684bd-0e40-4ad5-96cb-c441145ffc48

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralTraceNormBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PackingSeparation
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PackingSeparation_one_le_abs_norm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IntegralTraceNormBounds_prod_norm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PackingSeparation
open NumberField InfinitePlace Module MeasureTheory Metric TraceIntegralBasis IntegralTraceNormBounds
open scoped Classical
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD.PackingSeparation
theorem _root_.solution (γ : 𝓞 E) (hγ : γ ≠ 0) : ∃ w : CP E, 1 ≤ ‖w.1.embedding (γ : E)‖ := by
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace E))
  set w1 : CP E := ⟨w0, IsTotallyComplex.isComplex w0⟩
  have h := prod_norm (E := E) (γ : E)
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w1)] at h
  have hle : ∏ w ∈ Finset.univ.erase w1, ‖w.1.embedding (γ : E)‖ ^ 2 ≤ 1 :=
    Finset.prod_le_one (fun _ _ => by positivity)
      (fun w _ => pow_le_one₀ (norm_nonneg _) (hcon w).le)
  have hlt : ‖w1.1.embedding (γ : E)‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg _) (hcon w1) two_ne_zero
  have := one_le_abs_norm γ hγ
  rw [← h] at this
  nlinarith [mul_le_of_le_one_right (sq_nonneg ‖w1.1.embedding (γ : E)‖) hle]
end ReciprocityTheory.ChartRestriction.G.FD.PackingSeparation
