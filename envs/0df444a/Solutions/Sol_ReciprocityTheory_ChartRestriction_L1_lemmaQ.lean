-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.lemmaQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:08:06.250588+00:00
-- url     : https://prove2.me/submissions/72dd5f1d-3290-4454-979d-a2debec28e7c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_HD_coeff_one_A
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_HD_norm_a
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_eigen_trick
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_L1_divBy_C_mul__2cea45c9b452
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_L1_derivative_C_mul__8ab789f3f25e
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_HD_qcls_sub
import Theorems.Thm_Formalism_LT_InvIntP_Low_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_LawD_deriv_integral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_desc_QCls
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_desc_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divBy_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divBy_expand_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_hon_deriv


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
theorem _root_.solution (hF : FrobField K l σ) (h : HD σ lam Φ A a) {D : PowerSeries K}
    (hD : QCls l Φ A a D) :
    ∃ Dp : PowerSeries K,
      QCls l (MvPowerSeries.map (σ.comp σ) Φ) (PowerSeries.map (σ.comp σ) A) a Dp ∧
      DivBy (l : K) (D - C (coeff 1 D) * lam - Dp.subst ((X : PowerSeries K) ^ (l ^ 2))) := by
  have hl0 : l ≠ 0 := hF.prime.ne_zero
  set E : PowerSeries K := D - C (coeff 1 D) * lam with hE
  have hEq : QCls l Φ A a E := h.qcls_sub hD
  have hE' : DivBy (l : K) (derivative K E) := by
    have := hon_deriv h.toLawD (l : K) D hD.add
    rwa [hE, map_sub, derivative_C_mul']
  have h1 : QCls l (MvPowerSeries.map σ Φ) (PowerSeries.map σ A) a (desc l E) :=
    desc_QCls hF h.Φ0 h.Φint h.A0 h.Aint h.norm_a hEq hE'
  have c1 := (desc_congr hF.prime hF.norm_l E hE').1
  have hσ := h.map hF
  have hs : ‖coeff 1 (desc l E)‖ ≤ ‖(l : K)‖ :=
    eigen_trick hσ.A0 _ h1.D0 h1.eig (by rw [hσ.coeff_one_A]; exact h.a_ne)
  have h1' : DivBy (l : K) (derivative K (desc l E)) := by
    have h2 := hon_deriv hσ.toLawD (l : K) _ h1.add
    have h3 := divBy_add h2 (divBy_C_mul' hs hσ.toLawD.deriv_integral)
    rwa [sub_add_cancel] at h3
  have h2 : QCls l (MvPowerSeries.map σ (MvPowerSeries.map σ Φ))
      (PowerSeries.map σ (PowerSeries.map σ A)) a (desc l (desc l E)) :=
    desc_QCls hF hσ.Φ0 hσ.Φint hσ.A0 hσ.Aint h.norm_a h1 h1'
  have c2 := (desc_congr hF.prime hF.norm_l _ h1').1
  refine ⟨desc l (desc l E), ?_, ?_⟩
  · have e1 : MvPowerSeries.map (σ.comp σ) Φ = MvPowerSeries.map σ (MvPowerSeries.map σ Φ) := by
      ext d; simp
    have e2 : PowerSeries.map (σ.comp σ) A = PowerSeries.map σ (PowerSeries.map σ A) := by
      ext d; simp
    rw [e1, e2]; exact h2
  · have hXl : HasSubst ((X : PowerSeries K) ^ l) :=
      HasSubst.of_constantCoeff_zero' (by simp [hl0])
    have c3 := (divBy_expand_iff (l : K) l hl0 _).2 c2
    rw [subst_sub hXl, subst_comp_subst_apply hXl hXl, subst_pow hXl, subst_X hXl, ← pow_mul,
      ← sq] at c3
    have c4 := divBy_add c1 c3
    rwa [sub_add_sub_cancel] at c4
end ReciprocityTheory.ChartRestriction.L1
