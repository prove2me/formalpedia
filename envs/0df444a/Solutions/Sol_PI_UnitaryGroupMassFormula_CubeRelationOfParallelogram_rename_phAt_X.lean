-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.rename_phAt_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:38:48.097476+00:00
-- url     : https://prove2.me/submissions/06f896f1-2652-4d22-9d00-0857d7e5f360

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_CoeffPowMulPowEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_IsExpIntegralParallelogramOfNe
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_rename_psubst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Classical
namespace PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
open PI.FglGram MvPowerSeries
variable {p : ℕ} [Fact p.Prime] {σ τ : Type*}
section
variable {l ex : PowerSeries ℂ_[p]} (ph : PowerSeries ℂ_[p])
  (hex : PowerSeries.constantCoeff ex = 0) (hl : PowerSeries.constantCoeff l = 0)
private theorem rename_embedding_X (e : σ ↪ τ) (i : σ) :
    rename e (X i : MvPowerSeries σ ℂ_[p]) = X (e i) :=
  rename_X e i
end
end PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
end
end

set_option autoImplicit false
noncomputable section
open Classical
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
open PI.FglGram MvPowerSeries
variable {p : ℕ} [Fact p.Prime] {σ τ : Type*}
variable {l ex : PowerSeries ℂ_[p]} (ph : PowerSeries ℂ_[p])
  (hex : PowerSeries.constantCoeff ex = 0) (hl : PowerSeries.constantCoeff l = 0)
namespace PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
theorem _root_.solution (e : σ ↪ τ) (i : σ) :
    rename e (phAt ph (Xv (p := p) i)) = phAt ph (Xv (e i)) := by
  have h0 : constantCoeff (PI.FglGram.Xv (p := p) i) = 0 := constantCoeff_X i
  have h1 : rename e (PI.FglGram.Xv (p := p) i) = PI.FglGram.Xv (e i) := rename_embedding_X e i
  simp only [PI.FglGram.phAt]
  rw [rename_psubst e h0, h1]
end PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
