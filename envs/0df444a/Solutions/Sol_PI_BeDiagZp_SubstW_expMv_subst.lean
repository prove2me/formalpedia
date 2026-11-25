-- Prove2me | solution 1 for PI.BeDiagZp.SubstW.expMv_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:54:05.387493+00:00
-- url     : https://prove2.me/submissions/56f91deb-1ce5-4355-b3a2-d9b437661ac6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_PowerSeriesDiagonalLinear
import Theorems.Thm_PI_BeDiagZp_SubstW_coeff_expMv_eq
import Theorems.Thm_PI_BeDiagZp_SubstW_coeff_expTr

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
open PI PI.BeDiagZp PI.BeDiagZp.SubstW
variable {p : ℕ} [Fact p.Prime]
namespace PI.BeDiagZp.SubstW
theorem _root_.solution {σ τ : Type*} [Finite σ] {s : σ → MvPowerSeries τ ℂ_[p]}
    (hs0 : ∀ i, MvPowerSeries.constantCoeff (s i) = 0) {F : MvPowerSeries σ ℂ_[p]}
    (hF : MvPowerSeries.constantCoeff F = 0) :
    expMv (MvPowerSeries.subst s F) = MvPowerSeries.subst s (expMv F) := by
  have hs : MvPowerSeries.HasSubst s := MvPowerSeries.hasSubst_of_constantCoeff_zero hs0
  have hE : MvPowerSeries.constantCoeff (MvPowerSeries.subst s F) = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero hs hs0 hF
  ext e
  have hD : ((e.degree + 1 : ℕ) : ℕ∞) ≤ (expMv F - expTr F (e.degree + 1)).order := by
    apply MvPowerSeries.le_order
    intro d hd
    have hd' : d.degree < e.degree + 1 := by exact_mod_cast hd
    rw [map_sub, coeff_expMv_eq hF d hd', coeff_expTr, sub_self]
  have h1 : (1 : ℕ∞) ≤ ⨅ i, (s i).order :=
    le_iInf fun i => MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr (hs0 i)
  have hsD : ((e.degree + 1 : ℕ) : ℕ∞) ≤
      (MvPowerSeries.subst s (expMv F - expTr F (e.degree + 1))).order := by
    refine le_trans ?_ (MvPowerSeries.le_order_subst hs _)
    calc ((e.degree + 1 : ℕ) : ℕ∞) ≤ (expMv F - expTr F (e.degree + 1)).order := hD
      _ = 1 * (expMv F - expTr F (e.degree + 1)).order := (one_mul _).symm
      _ ≤ _ := by
        first
          | exact mul_le_mul_right' h1 _
          | exact mul_le_mul_right h1 _
          | gcongr
  have h0 : MvPowerSeries.coeff e (MvPowerSeries.subst s (expMv F - expTr F (e.degree + 1))) = 0 :=
    MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self _) hsD)
  rw [MvPowerSeries.subst_sub hs, map_sub, sub_eq_zero] at h0
  rw [h0, coeff_expMv_eq hE e (Nat.lt_succ_self _), expTr, ← MvPowerSeries.coe_substAlgHom hs]
  simp only [map_sum, map_smul, map_pow, smul_eq_mul]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [div_eq_inv_mul]
end PI.BeDiagZp.SubstW
