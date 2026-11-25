-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_H_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:04:23.803375+00:00
-- url     : https://prove2.me/submissions/faf1f9d5-6ff1-4e15-807c-e9b355761c45

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepArith
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepHSelfInt
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_kappa_eq
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_conj_theta


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
variable (m : Type) [Fintype m] [DecidableEq m]
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (hOK : CmOK a b c d) (Λ : AddSubgroup (m → ℂ))
    (hΛ : IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λ) (hθ : ∀ z ∈ Λ, cmTheta b d • z ∈ Λ)
    {x y : m → ℂ} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    ∃ n c₂ : ℤ, stdH (cmL a b d ha hd lam hlam) m x y =
      repKappa a b d ha hd lam hlam * ((n : ℂ) - c₂ * conj (cmTheta b d)) ∧
      (stdH (cmL a b d ha hd lam hlam) m x y).im = c₂ := by
  have hxd : x ∈ dualLat (stdH (cmL a b d ha hd lam hlam) m) Λ := by
    rw [hΛ]
    exact hx
  obtain ⟨c₂, hc₂⟩ := hxd y hy
  obtain ⟨m', hm'⟩ := hxd (cmTheta b d • y) (hθ y hy)
  have hsm : stdH (cmL a b d ha hd lam hlam) m x (cmTheta b d • y) =
      conj (cmTheta b d) * stdH (cmL a b d ha hd lam hlam) m x y := by
    rw [LinearMap.map_smulₛₗ]
    rfl
  have him : (stdH (cmL a b d ha hd lam hlam) m x y).im = c₂ := hc₂
  have hs : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hsC : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'

  have hre : (b / 2 : ℝ) * c₂ - Real.sqrt d / 2 * (stdH (cmL a b d ha hd lam hlam) m x y).re = m' := by
    have h1 : (conj (cmTheta b d) * stdH (cmL a b d ha hd lam hlam) m x y).im = m' := by
      rw [← hsm]
      exact hm'
    rw [rep_conj_theta] at h1
    simp [Complex.mul_im, him] at h1
    linarith
  have hre' : (stdH (cmL a b d ha hd lam hlam) m x y).re = (b * c₂ - 2 * m') / Real.sqrt d := by
    field_simp
    linarith
  refine ⟨b * c₂ - m', c₂, ?_, him⟩
  rw [rep_kappa_eq, rep_conj_theta]
  calc stdH (cmL a b d ha hd lam hlam) m x y
      = ((stdH (cmL a b d ha hd lam hlam) m x y).re : ℂ) +
          ((stdH (cmL a b d ha hd lam hlam) m x y).im : ℂ) * Complex.I := (Complex.re_add_im _).symm
    _ = _ := by
      rw [hre', him]
      push_cast
      field_simp
      ring
end PI.UnitaryGroupMassFormula.UnimodLocStd
