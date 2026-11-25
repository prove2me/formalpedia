-- Prove2me | solution 1 for PI.AddIntG.Wk.rt_G_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:01:39.812496+00:00
-- url     : https://prove2.me/submissions/2e3c026e-65d0-4f29-8001-ee9a3bc0bdaa

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_ThirdRootSubVarZeroNeZero

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
open PI PI.AddIntG PI.AddIntG.Wk
variable {p : ℕ} [Fact p.Prime]
namespace PI.AddIntG.Wk
theorem _root_.solution {R R' : Type*} [CommRing R] [Algebra ℂ_[p] R] [CommRing R'] [Algebra ℂ_[p] R']
    (φ : R →ₐ[ℂ_[p]] R') (W : WeierstrassCurve ℂ_[p]) (u v : R) :
    φ (G W u v) = G W (φ u) (φ v) := by
  simp only [G, map_add, map_sub, map_mul, map_pow, AlgHom.commutes]
end PI.AddIntG.Wk
