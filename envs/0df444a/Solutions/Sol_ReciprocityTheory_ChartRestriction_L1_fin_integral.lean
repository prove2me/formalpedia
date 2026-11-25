-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.fin_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:20:24.931056+00:00
-- url     : https://prove2.me/submissions/8d901a08-32ed-4285-946a-8351ee7de511

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffOneSubstOfConstantCoeffEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_SemilinNormPowSubPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgFinA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_FrobField_funEqSetting_sq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_ltLog_type
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_isFunEqType_of_mv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_inv_mul_inv_eq_of_eq_mul
import Theorems.Thm_Formalism_LT_funEqHom
import Theorems.Thm_Formalism_LT_funEqSubst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralPS_C
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralPS_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralPS_iff_mv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralPS_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_ltLog_const


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
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution [CompleteSpace K] (hF : FrobField K l σ) (ex lam : PowerSeries K)
    (hlam0 : constantCoeff lam = 0) (hlam1 : coeff 1 lam = 1) (hex0 : constantCoeff ex = 0)
    (hinv : ex.subst lam = X) (c ε : K) (hc : ‖c‖ = 1) (hε : ‖ε‖ = 1) (hcε : ε = c * σ (σ ε))
    (hT : IntegralPS (lam - (c / (l : K)) •
      (PowerSeries.map (σ.comp σ) lam).subst ((X : PowerSeries K) ^ (l ^ 2)))) :
    IntegralPS (ex.subst (C ε * ltLog K l)) := by
  have hl2 : 2 ≤ l := hF.prime.two_le
  have hq : l ^ 2 ≠ 0 := pow_ne_zero 2 hF.prime.ne_zero
  have hS := hF.funEqSetting_sq
  have hε0 : ε ≠ 0 := fun h => by simp [h] at hε
  have hτε0 : σ (σ ε) ≠ 0 := fun h => hε0 (by rw [hcε, h, mul_zero])
  have hXq : PowerSeries.HasSubst ((X : PowerSeries K) ^ (l ^ 2)) := PowerSeries.HasSubst.X_pow hq

  set f0 : PowerSeries K := ε⁻¹ • lam with hf0
  have hf00 : constantCoeff f0 = 0 := by
    rw [hf0, ← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_smul,
      coeff_zero_eq_constantCoeff_apply, hlam0, smul_zero]
  have hf0T : IsFunEqType l (l ^ 2) (σ.comp σ) f0 := by
    unfold IsFunEqType
    have e : f0 - (l : K)⁻¹ • (PowerSeries.map (σ.comp σ) f0).subst ((X : PowerSeries K) ^ (l ^ 2))
        = C ε⁻¹ * (lam - (c / (l : K)) •
          (PowerSeries.map (σ.comp σ) lam).subst ((X : PowerSeries K) ^ (l ^ 2))) := by
      have e1 : PowerSeries.map (σ.comp σ) f0 = (σ (σ ε))⁻¹ • PowerSeries.map (σ.comp σ) lam := by
        ext n
        rw [hf0, coeff_map, PowerSeries.coeff_smul, PowerSeries.coeff_smul, coeff_map, smul_eq_mul,
          smul_eq_mul, map_mul, map_inv₀]
        rfl
      rw [e1, PowerSeries.subst_smul hXq, smul_smul, ← smul_eq_C_mul, smul_sub, smul_smul, hf0]
      congr 2
      have hc0 : c ≠ 0 := fun h => by simp [h] at hc
      exact inv_mul_inv_eq_of_eq_mul c ε _ _ hc0 hcε
    rw [e]
    exact integralPS_mul (integralPS_C (by rw [norm_inv, hε, inv_one])) hT

  set α : PowerSeries K := C ε * X with hα
  have hα0 : constantCoeff α = 0 := by rw [hα, map_mul, constantCoeff_X, mul_zero]
  have hαs : PowerSeries.HasSubst α := PowerSeries.HasSubst.of_constantCoeff_zero' hα0
  have hαI : IntegralPS α := integralPS_mul (integralPS_C hε.le) integralPS_X
  set f1 : PowerSeries K := f0.subst α with hf1
  have hf1T : IsFunEqType l (l ^ 2) (σ.comp σ) f1 :=
    isFunEqType_of_mv hq _ _ (Formalism.LT.funEqSubst K l (l ^ 2) hq (σ.comp σ) hS f0 hf00 hf0T Unit α
      hα0 ((integralPS_iff_mv α).1 hαI))
  have hf1e : f1 = ε⁻¹ • PowerSeries.rescale ε lam := by
    rw [hf1, hf0, PowerSeries.subst_smul hαs, PowerSeries.rescale_eq_subst, hα, ← smul_eq_C_mul]
  have hf10 : constantCoeff f1 = 0 := by
    rw [hf1e, ← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_smul, coeff_rescale,
      coeff_zero_eq_constantCoeff_apply, hlam0]; simp
  have hf11 : coeff 1 f1 = 1 := by
    rw [hf1e, PowerSeries.coeff_smul, coeff_rescale, hlam1, pow_one, mul_one, smul_eq_mul,
      inv_mul_cancel₀ hε0]
  obtain ⟨h, hh0, hhI, hh⟩ := Formalism.LT.funEqHom K l (l ^ 2) (σ.comp σ) hS f1 (ltLog K l) hf10 hf11
    hf1T (ltLog_const l hl2) (ltLog_type hl2 _)
  have hhs : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero' hh0
  have hβ0 : constantCoeff (C ε * h) = 0 := by rw [map_mul, hh0, mul_zero]
  have hβs : PowerSeries.HasSubst (C ε * h) := PowerSeries.HasSubst.of_constantCoeff_zero' hβ0
  have hlams : PowerSeries.HasSubst lam := PowerSeries.HasSubst.of_constantCoeff_zero' hlam0
  have e2 : α.subst h = C ε * h := by
    rw [hα, PowerSeries.subst_mul hhs, PowerSeries.subst_X hhs, PowerSeries.subst_C]; rfl
  have e3 : lam.subst (C ε * h) = C ε * ltLog K l := by
    rw [← hh, hf1, PowerSeries.subst_comp_subst_apply hαs hhs, e2, hf0,
      PowerSeries.subst_smul hβs, smul_eq_C_mul, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hε0,
      map_one, one_mul]
  rw [← e3, ← PowerSeries.subst_comp_subst_apply hlams hβs, hinv, PowerSeries.subst_X hβs]
  exact integralPS_mul (integralPS_C hε.le) hhI
end ReciprocityTheory.ChartRestriction.L1
