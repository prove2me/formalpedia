-- Prove2me | solution 1 for PI.BeDiagZp.simeq_equivalence_additive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:09:38.782178+00:00
-- url     : https://prove2.me/submissions/55d9637b-327b-4d0a-9302-02d0eac4682a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_CoeffPowMulPowEqZeroOfLt
import Theorems.Thm_PI_BeDiagZp_simeq_refl
import Theorems.Thm_PI_BeDiagZp_simeq_symm
import Theorems.Thm_PI_BeDiagZp_simeq_add
import Theorems.Thm_PI_BeDiagZp_simeq_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.BeDiagZp
open MvPowerSeries
open IntegralPowerSeriesBall
variable {p : ℕ} [Fact p.Prime] {σ : Type*}
namespace PI.BeDiagZp
theorem _root_.solution : S0 := fun _ _ _ f _ _ _ _ =>
  ⟨simeq_refl f, simeq_symm, simeq_trans, simeq_add⟩
end PI.BeDiagZp
