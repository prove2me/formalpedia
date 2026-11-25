-- Prove2me | solution 1 for P2M_PI_ClassNumImQ_ZetaNonvanishing__le_of_mul_eq_4de6eaa66ab0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:46:54.124779+00:00
-- url     : https://prove2.me/submissions/cf850094-297f-4cf9-b872-5f26807da3f1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ClassNumImQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDedekindZeta_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDedekindZeta_SpanNatCastSupEqTop
import Theorems.Thm_P2M_PI_ClassNumImQ_ZetaNonvanishing__span_natCast_sup_eq_top_26fc201e2cd4
import Theorems.Thm_P2M_PI_ClassNumImQ_ZetaNonvanishing__span_le_of_absNorm_fd6c4dee4894

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open PI PI.ClassNumImQ PI.ClassNumImQ.ZetaNonvanishing₂
variable {K : Type} [Field K] [NumberField K]
namespace PI.ClassNumImQ.ZetaNonvanishing₂
theorem _root_.solution {m n : ℕ} (hmn : m.Coprime n) {I J I' J' : Ideal (𝓞 K)}
    (hI : Ideal.absNorm I = m) (hJ' : Ideal.absNorm J' = n) (h : I * J = I' * J') : I' ≤ I := by
  have hcop : IsCoprime I J' := by
    rw [Ideal.isCoprime_iff_sup_eq, eq_top_iff, ← span_natCast_sup_eq_top hmn]
    exact sup_le_sup (span_le_of_absNorm hI) (span_le_of_absNorm hJ')
  have hd : I ∣ I' * J' := ⟨J, h.symm⟩
  exact Ideal.le_of_dvd (hcop.dvd_of_dvd_mul_right hd)
end PI.ClassNumImQ.ZetaNonvanishing₂
