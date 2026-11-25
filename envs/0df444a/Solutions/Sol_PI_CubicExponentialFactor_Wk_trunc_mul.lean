-- Prove2me | solution 1 for PI.CubicExponentialFactor.Wk.trunc_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:34:11.870423+00:00
-- url     : https://prove2.me/submissions/a9931a16-cf68-4ba5-bc0d-28f7d0391687

import Definitions.Def_Formalism_PeriodIntegrals_CubicExponentialFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubicExponentialFactor_NormAddLeOne
import Theorems.Thm_PI_CubicExponentialFactor_Wk_norm_add_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CubicExponentialFactor PI.CubicExponentialFactor.Wk
open PI.CubicExponentialFactor
variable {p : ℕ} [Fact p.Prime]
namespace PI.CubicExponentialFactor.Wk
theorem _root_.solution {f g : PowerSeries ℂ_[p]} {k : ℕ} (hf : ∀ j < k, ‖PowerSeries.coeff j f‖ ≤ 1)
    (hg : ∀ j < k, ‖PowerSeries.coeff j g‖ ≤ 1) : ∀ j < k, ‖PowerSeries.coeff j (f * g)‖ ≤ 1 := by
  classical
  intro j hj
  rw [PowerSeries.coeff_mul]
  have key : ∀ s : Finset (ℕ × ℕ), (∀ q ∈ s, q.1 + q.2 = j) →
      ‖∑ q ∈ s, PowerSeries.coeff q.1 f * PowerSeries.coeff q.2 g‖ ≤ 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | insert q s hq ih =>
      intro hs
      rw [Finset.sum_insert hq]
      have hq' := hs q (Finset.mem_insert_self q s)
      refine norm_add_le_one ?_ (ih fun q' h' => hs q' (Finset.mem_insert_of_mem h'))
      rw [norm_mul]
      exact mul_le_one₀ (hf _ (by omega)) (norm_nonneg _) (hg _ (by omega))
  exact key _ (fun q h => by simpa using h)
end PI.CubicExponentialFactor.Wk
