-- Prove2me | solution 1 for PI.BeDiagZp.IntegralPowerSeriesBall.intMv_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:35:06.192285+00:00
-- url     : https://prove2.me/submissions/f44c12d5-9677-4bef-9a72-159ecdd18a9d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_CoeffPowMulPowEqZeroOfLt

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
open PI.BeDiagZp.IntegralPowerSeriesBall
variable {p : ℕ} [Fact p.Prime] {σ : Type*}
namespace PI.BeDiagZp.IntegralPowerSeriesBall
theorem _root_.solution {F : MvPowerSeries σ ℂ_[p]} (hF : IntegralMv F) (h1 : constantCoeff F = 1) :
    ∃ G : MvPowerSeries σ ℂ_[p], IntegralMv G ∧ F * G = 1 := by
  let F' : MvPowerSeries σ (ballSub p) := fun n => ⟨coeff n F, hF n⟩
  have hmap : map (ballSub p).subtype F' = F := by
    ext n; rw [coeff_map]; rfl
  have hc : constantCoeff F' = 1 := by
    apply Subtype.val_injective
    have := constantCoeff_map (ballSub p).subtype F'
    rw [hmap, h1] at this
    simpa using this.symm
  have hG' : F' * invOfUnit F' 1 = 1 := mul_invOfUnit F' 1 (by rw [hc, Units.val_one])
  refine ⟨map (ballSub p).subtype (invOfUnit F' 1), fun n => ?_, ?_⟩
  · rw [coeff_map]; exact (coeff n (invOfUnit F' 1)).2
  · rw [← hmap, ← map_mul, hG', map_one]
end PI.BeDiagZp.IntegralPowerSeriesBall
