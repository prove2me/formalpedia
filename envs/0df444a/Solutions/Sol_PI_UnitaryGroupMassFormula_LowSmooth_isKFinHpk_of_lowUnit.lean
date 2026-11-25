-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:54:24.42378+00:00
-- url     : https://prove2.me/submissions/2eda4afe-1f4b-48c8-95f8-6d1e7b34a6cc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_LowCyc
import Definitions.Def_Formalism_PeriodIntegrals_KFinSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerSmoothStability_ExistsFinStableOfMemSSup
import Theorems.Thm_PI_UnitaryGroupMassFormula_LowSmooth_exists_finStable_of_mem_sSup
import Theorems.Thm_PI_UnitaryGroupMassFormula_LowSmooth_conj_mem_Kset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LowSmooth
open PI.UpqRep
namespace PI.UnitaryGroupMassFormula.LowSmooth
theorem _root_.solution {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} {w : H}
    (hlow : IsLowUnitH k r ε lam σ w) : IsKFinHpk (k := k) (r := r) σ w := by
  obtain ⟨P, hP, -, hw⟩ := hlow
  obtain ⟨S, ⟨hfin, hst⟩, hwS⟩ := exists_finStable_of_mem_sSup (Kset ε) (fun h => σ (P⁻¹ * h * P))
    (F := {S | IsKTypeOf ε (fun h => σ (P⁻¹ * h * P)) (lowK ε lam) S})
    (fun S hS => ⟨hS.1, hS.2.1⟩) hw
  refine ⟨S, hfin, hwS, fun g hg x hx => ?_⟩
  obtain ⟨hK, hback⟩ := conj_mem_Kset hP hg
  have := hst _ hK x hx
  beta_reduce at this
  rwa [hback] at this
end PI.UnitaryGroupMassFormula.LowSmooth
