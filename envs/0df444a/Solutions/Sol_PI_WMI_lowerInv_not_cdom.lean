-- Prove2me | solution 1 for PI.WMI.lowerInv_not_cdom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:10:18.382146+00:00
-- url     : https://prove2.me/submissions/acb8baa8-ef16-475c-bebd-a2090577d32d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_LowerInv
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WMI
open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace
namespace PI.WMI
theorem _root_.solution {N : ℕ} {Λ : Fin N → ℝ} {a b : Fin N} (hab : a < b) {m : ℕ} (hm : 1 ≤ m) :
    ¬ CDom (allPos N) (Λ + (m : ℝ) • root a b) Λ := by
  rintro ⟨cc, hcc, heq⟩
  let L : (Fin N → ℝ) →ₗ[ℝ] ℝ := ∑ x : Fin N, ((x : ℕ) : ℝ) • LinearMap.proj x
  have hL : ∀ v, L v = ∑ x : Fin N, ((x : ℕ) : ℝ) * v x := by
    intro v; simp [L, LinearMap.sum_apply]
  have hroot : ∀ x y : Fin N, L (root x y) = ((x : ℕ) : ℝ) - ((y : ℕ) : ℝ) := by
    intro x y
    rw [hL]
    simp [root, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]
  have h1 := congrArg L heq
  simp only [map_sum, map_smul, hroot] at h1
  have lhs : L (Λ - (Λ + (m : ℝ) • root a b)) = (m : ℝ) * (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
    rw [sub_add_cancel_left, map_neg, map_smul, hroot, smul_eq_mul]; ring
  rw [lhs] at h1
  have hle : ∑ x, ∑ y, (cc x y : ℝ) • (((x : ℕ) : ℝ) - ((y : ℕ) : ℝ)) ≤ 0 :=
    Finset.sum_nonpos fun x _ => Finset.sum_nonpos fun y _ => by
      by_cases h : cc x y = 0
      · simp [h]
      · have hxy : (x : ℕ) < y := (hcc x y h).1
        rw [smul_eq_mul]
        apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
        rw [sub_nonpos]; exact_mod_cast hxy.le
  have hpos : 0 < (m : ℝ) * (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
    apply mul_pos (by exact_mod_cast hm)
    rw [sub_pos]; exact_mod_cast hab
  linarith
end PI.WMI
