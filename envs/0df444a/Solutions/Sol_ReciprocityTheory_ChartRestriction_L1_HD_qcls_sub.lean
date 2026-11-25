-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.HD.qcls_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:51:33.66209+00:00
-- url     : https://prove2.me/submissions/5dd8a432-8fa8-45e0-905e-4784b03d9a3f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_subst_C_mul_mv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_subst_C_mul_ps
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_L1_derivative_C_mul__8ab789f3f25e
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_QCls_norm_coeff_one
import Theorems.Thm_Formalism_G_LogP_hX0
import Theorems.Thm_Formalism_G_LogP_hX1
import Theorems.Thm_Formalism_LT_InvIntP_Low_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_LawD_deriv_integral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}
variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}
namespace ReciprocityTheory.ChartRestriction.L1
namespace HD
theorem _root_.solution (h : HD σ lam Φ A a) {D : PowerSeries K} (hD : QCls l Φ A a D) :
    QCls l Φ A a (D - C (coeff 1 D) * lam) := by
  set c := coeff 1 D with hc
  have hc1 : ‖c‖ ≤ 1 := hD.norm_coeff_one
  have hΦ : HasSubst Φ := HasSubst.of_constantCoeff_zero h.Φ0
  have hA : HasSubst A := HasSubst.of_constantCoeff_zero h.A0
  have hX0 : HasSubst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) :=
    HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 0)
  have hX1 : HasSubst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) :=
    HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 1)
  have sub_subst : ∀ {P : MvPowerSeries (Fin 2) K} (_ : HasSubst P) (f g : PowerSeries K),
      (f - g).subst P = f.subst P - g.subst P := fun hP f g => by
    rw [← coe_substAlgHom hP, map_sub]
  have sub_substA : (D - C c * lam).subst A = D.subst A - C c * lam.subst A := by
    rw [← coe_substAlgHom hA, map_sub, coe_substAlgHom hA, subst_C_mul_ps hA]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hD.D0, h.lam0]
  · have hd := hD.dInt
    have hl := h.toLawD.deriv_integral
    unfold IntegralPS at hd hl ⊢
    intro n
    rw [map_sub, derivative_C_mul', map_sub, coeff_C_mul, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hd n) ?_)
    rw [norm_neg, norm_mul]
    calc ‖c‖ * ‖coeff n (derivative K lam)‖ ≤ 1 * 1 :=
          mul_le_mul hc1 (hl n) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · have e : (D - C c * lam).subst Φ - atX (D - C c * lam) - atY (D - C c * lam) =
        (D.subst Φ - atX D - atY D) - MvPowerSeries.C c * (lam.subst Φ - atX lam - atY lam) := by
      unfold atX atY
      rw [sub_subst hΦ, sub_subst hX0, sub_subst hX1, subst_C_mul_mv hΦ, subst_C_mul_mv hX0,
        subst_C_mul_mv hX1]
      ring
    have e2 : lam.subst Φ - atX lam - atY lam = 0 := by rw [h.log]; ring
    rw [e, e2, mul_zero, sub_zero]
    exact hD.add
  · have e : (D - C c * lam).subst A - C a * (D - C c * lam) = D.subst A - C a * D := by
      rw [sub_substA, h.Alog]
      ring
    rw [e]
    exact hD.eig
end HD
end ReciprocityTheory.ChartRestriction.L1
