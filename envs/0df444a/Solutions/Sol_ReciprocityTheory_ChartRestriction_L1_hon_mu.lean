-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.hon_mu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:58:51.500126+00:00
-- url     : https://prove2.me/submissions/8b4dc1ca-3ac9-4499-b5d9-abafe66d58eb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_SubstOfLog
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_HD_map_frobenius_sq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_honF_subst_subst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_honF_integral_subst
import Theorems.Thm_Formalism_G_LogP_hX0
import Theorems.Thm_Formalism_LT_Asm_integralMv_X
import Theorems.Thm_Formalism_LT_InvIntP_Low_add
import Theorems.Thm_Formalism_LT_InvIntP_key
import Theorems.Thm_Formalism_LT_PadicP_coeff_one_subst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_LawD_deriv_integral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_subst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_subst2
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralPS_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralPS_derivative
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralPS_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralPS_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_qls
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_qls1


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
theorem _root_.solution (hF : FrobField K l σ) (h : HD σ lam Φ A a) {e hh : PowerSeries K}
    (he0 : constantCoeff e = 0) (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam)
    (hh1 : HomCls l (MvPowerSeries.map (σ.comp σ) Φ) (PowerSeries.map (σ.comp σ) A) Φ A hh)
    (hh2 : DivBy (l : K) (e - hh.subst ((X : PowerSeries K) ^ (l ^ 2)))) :
    QCls l (MvPowerSeries.map (σ.comp σ) Φ) (PowerSeries.map (σ.comp σ) A) a (lam.subst hh) ∧
      DivBy (l : K) (C (l : K) * lam - PowerSeries.subst ((X : PowerSeries K) ^ (l ^ 2)) (lam.subst hh : PowerSeries K)) ∧
      coeff 1 (lam.subst hh) = coeff 1 hh := by
  have hl := hF.prime
  have hl1 := hF.norm_l
  have hlam' : IntegralPS (derivative K lam) := h.toLawD.deriv_integral
  have h' := h.map_frobenius_sq hF
  have Hh : PowerSeries.HasSubst hh := PowerSeries.HasSubst.of_constantCoeff_zero' hh1.g0
  have HΦ' : PowerSeries.HasSubst (MvPowerSeries.map (σ.comp σ) Φ) :=
    PowerSeries.HasSubst.of_constantCoeff_zero h'.Φ0
  have HA' : PowerSeries.HasSubst (PowerSeries.map (σ.comp σ) A) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' h'.A0
  have HA : PowerSeries.HasSubst A := PowerSeries.HasSubst.of_constantCoeff_zero' h.A0
  have hq : l ^ 2 ≠ 0 := pow_ne_zero _ hl.ne_zero
  have hXq0 : constantCoeff ((X : PowerSeries K) ^ (l ^ 2)) = 0 := by
    rw [map_pow, constantCoeff_X, zero_pow hq]
  have HXq : PowerSeries.HasSubst ((X : PowerSeries K) ^ (l ^ 2)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hXq0
  have hX0 : ∀ i : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  have HX : ∀ i : Fin 2, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) :=
    fun i => PowerSeries.HasSubst.of_constantCoeff_zero (hX0 i)
  have hp0 : ∀ i : Fin 2, MvPowerSeries.constantCoeff (![atX hh, atY hh] i) = 0 := by
    intro i
    fin_cases i
    · exact PowerSeries.constantCoeff_subst_eq_zero (hX0 0) hh hh1.g0
    · exact PowerSeries.constantCoeff_subst_eq_zero (hX0 1) hh hh1.g0
  have hpI : ∀ i : Fin 2, IntegralMv (![atX hh, atY hh] i) := by
    intro i
    fin_cases i
    · exact integralMv_subst hh1.gInt (hX0 0) (integralMv_X 0)
    · exact integralMv_subst hh1.gInt (hX0 1) (integralMv_X 1)
  have Hp : MvPowerSeries.HasSubst ![atX hh, atY hh] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hp0
  refine ⟨⟨PowerSeries.constantCoeff_subst_eq_zero hh1.g0 lam h.lam0, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [derivative_subst Hh]
    exact integralPS_mul (honF_integral_subst hlam' hh1.g0 hh1.gInt) (integralPS_derivative hh1.gInt)
  · have key := qls hl hl1 lam h.lam0 hlam' (hh.subst (MvPowerSeries.map (σ.comp σ) Φ))
      (Φ.subst ![atX hh, atY hh])
      (PowerSeries.constantCoeff_subst_eq_zero h'.Φ0 hh hh1.g0)
      (MvPowerSeries.constantCoeff_subst_eq_zero Hp hp0 h.Φ0)
      (integralMv_subst hh1.gInt h'.Φ0 h'.Φint) (integralMv_subst2 h.Φint hp0 hpI) hh1.add
    have ex : atX (lam.subst hh) = lam.subst (atX hh) :=
      PowerSeries.subst_comp_subst_apply Hh (HX 0) lam
    have ey : atY (lam.subst hh) = lam.subst (atY hh) :=
      PowerSeries.subst_comp_subst_apply Hh (HX 1) lam
    have ax : (atX lam).subst ![atX hh, atY hh] = lam.subst (atX hh) :=
      (honF_subst_subst lam (hX0 0) Hp).trans (by rw [MvPowerSeries.subst_X Hp]; rfl)
    have ay : (atY lam).subst ![atX hh, atY hh] = lam.subst (atY hh) :=
      (honF_subst_subst lam (hX0 1) Hp).trans (by rw [MvPowerSeries.subst_X Hp]; rfl)
    have e1 : lam.subst (Φ.subst ![atX hh, atY hh]) = atX (lam.subst hh) + atY (lam.subst hh) := by
      rw [ex, ey, ← honF_subst_subst lam h.Φ0 Hp, h.log, MvPowerSeries.subst_add Hp, ax, ay]
    rw [e1] at key
    rw [PowerSeries.subst_comp_subst_apply Hh HΦ', sub_sub]
    exact key
  · have key := qls1 hl hl1 lam h.lam0 hlam' (hh.subst (PowerSeries.map (σ.comp σ) A))
      (A.subst hh) (PowerSeries.constantCoeff_subst_eq_zero h'.A0 hh hh1.g0)
      (PowerSeries.constantCoeff_subst_eq_zero hh1.g0 A h.A0)
      (honF_integral_subst hh1.gInt h'.A0 h'.Aint) (honF_integral_subst h.Aint hh1.g0 hh1.gInt) hh1.eig
    rw [← PowerSeries.subst_comp_subst_apply HA Hh, h.Alog, PowerSeries.subst_mul Hh,
      PowerSeries.subst_C] at key
    rw [PowerSeries.subst_comp_subst_apply Hh HA']
    exact key
  · have key := qls1 hl hl1 lam h.lam0 hlam' e (hh.subst ((X : PowerSeries K) ^ (l ^ 2))) he0
      (PowerSeries.constantCoeff_subst_eq_zero hXq0 hh hh1.g0) he
      (honF_integral_subst hh1.gInt hXq0 (integralPS_pow integralPS_X _)) hh2
    rw [hlog] at key
    rw [PowerSeries.subst_comp_subst_apply Hh HXq]
    exact key
  · rw [Formalism.LT.PadicP.coeff_one_subst lam hh h.lam0 hh1.g0, h.lam1, one_mul]
end ReciprocityTheory.ChartRestriction.L1
