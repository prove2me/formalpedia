-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.isExpIntegral_parallelogram_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:54:01.008133+00:00
-- url     : https://prove2.me/submissions/70feb3b3-f389-4ab9-9be3-f872a0f7ac8c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_CoeffPowMulPowEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_IsExpIntegralParallelogramOfNe
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_good_rename
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_rename_phAt_add
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_rename_phAt_sub
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_rename_phAt_X
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_simeq_iff_good

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
include hex hl
namespace PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
theorem _root_.solution (i j : Fin 3) (hij : i ≠ j)
    (hE1 : Simeq (phAt ph (add l ex (Xv 0) (Xv 1)) + phAt ph (sub l ex (Xv 0) (Xv 1)) :
        MvPowerSeries (Fin 2) ℂ_[p]) (2 * phAt ph (Xv 0) + 2 * phAt ph (Xv 1))) :
    Good (phAt ph (add l ex (Xv i) (Xv j)) + phAt ph (sub l ex (Xv i) (Xv j)) -
      (2 * phAt ph (Xv i) + 2 * phAt ph (Xv j)) : MvPowerSeries (Fin 3) ℂ_[p]) := by
  have hinj : Function.Injective ![i, j] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      first
      | rfl
      | simp_all
  let e : Fin 2 ↪ Fin 3 := ⟨![i, j], hinj⟩
  have c0 : constantCoeff (PI.FglGram.Xv (p := p) (0 : Fin 2)) = 0 := constantCoeff_X _
  have c1 : constantCoeff (PI.FglGram.Xv (p := p) (1 : Fin 2)) = 0 := constantCoeff_X _
  have r0 : rename e (PI.FglGram.Xv (p := p) (0 : Fin 2)) = PI.FglGram.Xv i := rename_embedding_X e 0
  have r1 : rename e (PI.FglGram.Xv (p := p) (1 : Fin 2)) = PI.FglGram.Xv j := rename_embedding_X e 1
  have qa : rename e (PI.FglGram.phAt ph (PI.FglGram.add l ex (PI.FglGram.Xv (p := p) (0 : Fin 2)) (PI.FglGram.Xv 1))) =
      PI.FglGram.phAt ph (PI.FglGram.add l ex (PI.FglGram.Xv i) (PI.FglGram.Xv j)) := by
    rw [rename_phAt_add ph hex hl e _ _ c0 c1, r0, r1]
  have qs : rename e (PI.FglGram.phAt ph (PI.FglGram.sub l ex (PI.FglGram.Xv (p := p) (0 : Fin 2)) (PI.FglGram.Xv 1))) =
      PI.FglGram.phAt ph (PI.FglGram.sub l ex (PI.FglGram.Xv i) (PI.FglGram.Xv j)) := by
    rw [rename_phAt_sub ph hex hl e _ _ c0 c1, r0, r1]
  have q0 : rename e (PI.FglGram.phAt ph (PI.FglGram.Xv (p := p) (0 : Fin 2))) = PI.FglGram.phAt ph (PI.FglGram.Xv i) :=
    rename_phAt_X ph e 0
  have q1 : rename e (PI.FglGram.phAt ph (PI.FglGram.Xv (p := p) (1 : Fin 2))) = PI.FglGram.phAt ph (PI.FglGram.Xv j) :=
    rename_phAt_X ph e 1
  have h2 := good_rename e ((simeq_iff_good _ _).1 hE1)
  simp only [map_sub, map_add, map_mul, map_ofNat, qa, qs, q0, q1] at h2
  exact h2
end PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
