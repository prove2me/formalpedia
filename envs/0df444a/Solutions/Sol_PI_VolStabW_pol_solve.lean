-- Prove2me | solution 1 for PI.VolStabW.pol_solve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:01:29.337044+00:00
-- url     : https://prove2.me/submissions/a6ab01a1-47ae-4923-b0d7-dd27c92d3680

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVDx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHH

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  Matrix
variable {A : Type} [CommRing A] (s : A →+* A)
namespace PI.VolStabW
theorem _root_.solution {a : ℕ} (h πA : A) (hh : h + h = 1) (hsh : s h = h)
    (Γ Tm Tinv Sm E0 : Matrix (Fin a) (Fin a) A) (hΓ : Γ = Tm + πA • E0)
    (hTT : Tm * Tinv = 1) (hTs : (Tinv.map s)ᵀ * Tm = 1) (hS : ∀ i k, s (Sm k i) = Sm i k) :
    Γ * ((h • (Tinv * Sm))ᵀ)ᵀ + ((h • (Tinv * Sm))ᵀ).map s * Γ =
      Sm + πA • (h • (E0 * Tinv * Sm + Sm * (Tinv.map s)ᵀ * E0)) := by
  set Ts := (Tinv.map s)ᵀ with hTsdef
  have hC1 : ((h • (Tinv * Sm))ᵀ)ᵀ = h • (Tinv * Sm) := transpose_transpose _
  have hC2 : ((h • (Tinv * Sm))ᵀ).map s = h • (Sm * Ts) := by
    ext i j
    simp only [hTsdef, Matrix.map_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.mul_apply,
      smul_eq_mul, map_mul, map_sum, hsh, hS]
    congr 1
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  calc Γ * ((h • (Tinv * Sm))ᵀ)ᵀ + ((h • (Tinv * Sm))ᵀ).map s * Γ
      = (Tm + πA • E0) * (h • (Tinv * Sm)) + h • (Sm * Ts) * (Tm + πA • E0) := by
        rw [hC1, hC2, hΓ]
    _ = h • ((Tm * Tinv) * Sm) + (πA * h) • (E0 * Tinv * Sm) +
          (h • (Sm * (Ts * Tm)) + (h * πA) • (Sm * Ts * E0)) := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.mul_assoc, smul_smul]
        try module
    _ = (h + h) • Sm + πA • (h • (E0 * Tinv * Sm + Sm * Ts * E0)) := by
        rw [hTT, hTs, Matrix.one_mul, Matrix.mul_one]
        module
    _ = _ := by rw [hh, one_smul]
end PI.VolStabW
