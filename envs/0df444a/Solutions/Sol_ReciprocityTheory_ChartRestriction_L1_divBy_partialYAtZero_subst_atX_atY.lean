-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.divBy_partialYAtZero_subst_atX_atY
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:45:10.892735+00:00
-- url     : https://prove2.me/submissions/044b73a0-8067-4a7e-9261-1bd5b30f4395

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_DivByPartialYAtZeroSubstAtXAtY
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_homE_norm_coeff_atX_mul_atY
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_homE_norm_coeff_one_pow
import Theorems.Thm_P2M_Formalism_LT_LTL_norm_finsum_le__8658a123f7be
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralPS_pow


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
variable {lam₁ lam₂ : PowerSeries K} {Φ₁ Φ₂ : MvPowerSeries (Fin 2) K} {A₁ A₂ g : PowerSeries K}
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {x : K} (hΦ₂ : IntegralMv Φ₂) (hg0 : constantCoeff g = 0)
    (hg : IntegralPS g) (h0 : ‖coeff 1 g‖ ≤ ‖x‖) :
    DivBy x (d2 (Φ₂.subst ![atX g, atY g])) := by
  intro n
  have hX : PowerSeries.HasSubst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K) :=
    PowerSeries.HasSubst.X 0
  have hY : PowerSeries.HasSubst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) :=
    PowerSeries.HasSubst.X 1
  have hP' : MvPowerSeries.HasSubst ![atX g, atY g] := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => ?_
    fin_cases i
    · exact PowerSeries.constantCoeff_subst_eq_zero (by simp) g hg0
    · exact PowerSeries.constantCoeff_subst_eq_zero (by simp) g hg0
  rw [d2, coeff_mk, MvPowerSeries.coeff_subst hP']
  refine Formalism.LT.LTL.norm_finsum_le' (norm_nonneg _) fun m => ?_
  rw [smul_eq_mul, norm_mul, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [atX, atY, ← PowerSeries.subst_pow hX, ← PowerSeries.subst_pow hY]
  have := homE_norm_coeff_atX_mul_atY (g ^ m 0) (g ^ m 1) (integralPS_pow hg _)
    (homE_norm_coeff_one_pow hg0 h0 _) n
  exact (mul_le_mul (hΦ₂ m) this (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
end ReciprocityTheory.ChartRestriction.L1
