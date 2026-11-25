-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.mulN_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:57:06.116109+00:00
-- url     : https://prove2.me/submissions/2cc0b2d6-c487-4c27-9808-0b3742344bce

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgMulN
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_powerSeries_subst_subst_of_constantCoeff_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_subst2
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralPS_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralPS_iff_mv


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
theorem _root_.solution {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} (h : LawD lam Φ) (n : ℕ) :
    ∃ e : PowerSeries K, constantCoeff e = 0 ∧ IntegralPS e ∧ lam.subst e = C (n : K) * lam := by
  have hXs : lam.subst (X : PowerSeries K) = lam := by
    have ha1 : PowerSeries.HasSubst (X : PowerSeries K) :=
      PowerSeries.HasSubst.of_constantCoeff_zero' PowerSeries.constantCoeff_X
    ext m
    rw [PowerSeries.coeff_subst' ha1]
    rw [finsum_eq_single _ m]
    · rw [PowerSeries.coeff_X_pow_self, smul_eq_mul, mul_one]
    · intro d hd
      rw [PowerSeries.coeff_X_pow, if_neg (Ne.symm hd), smul_zero]
  induction n with
  | zero =>
    refine ⟨0, map_zero _, by unfold IntegralPS; intro k; simp, ?_⟩
    ext k
    rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' (map_zero _)),
      Nat.cast_zero, map_zero, zero_mul, map_zero]
    apply finsum_eq_zero_of_forall_eq_zero
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, h.lam0, zero_smul]
    · rw [zero_pow hd.ne', map_zero, smul_zero]
  | succ n ih =>
    obtain ⟨e, he0, he, hlog⟩ := ih
    have hP0 : ∀ s, MvPowerSeries.constantCoeff ((![e, X] : Fin 2 → PowerSeries K) s) = 0 := by
      intro s
      fin_cases s
      · exact he0
      · exact PowerSeries.constantCoeff_X
    have hPint : ∀ s, IntegralMv ((![e, X] : Fin 2 → PowerSeries K) s) := by
      intro s
      fin_cases s
      · exact (integralPS_iff_mv e).mp he
      · exact (integralPS_iff_mv _).mp integralPS_X
    have ha : MvPowerSeries.HasSubst (![e, X] : Fin 2 → PowerSeries K) :=
      ⟨fun s => by rw [hP0 s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
    refine ⟨Φ.subst (![e, X] : Fin 2 → PowerSeries K), ?_, ?_, ?_⟩
    · have h0 : MvPowerSeries.constantCoeff (Φ.subst (![e, X] : Fin 2 → PowerSeries K)) = 0 := by
        rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_subst ha]
        apply finsum_eq_zero_of_forall_eq_zero
        intro d
        by_cases hd : d = 0
        · rw [hd, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h.Φ0, zero_smul]
        · obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
            by_contra hc
            push_neg at hc
            exact hd (Finsupp.ext hc)
          rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Finsupp.prod, map_prod,
            Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (by rw [map_pow, hP0 s, zero_pow hs]),
            smul_zero]
      exact h0
    · exact (integralPS_iff_mv _).mpr (integralMv_subst2 h.Φint hP0 hPint)
    · rw [← powerSeries_subst_subst_of_constantCoeff_zero lam h.Φ0 ha, h.log]
      unfold atX atY
      first
      | rw [MvPowerSeries.subst_add ha]
      | rw [← MvPowerSeries.coe_substAlgHom ha, map_add, MvPowerSeries.coe_substAlgHom]
      rw [powerSeries_subst_subst_of_constantCoeff_zero lam (MvPowerSeries.constantCoeff_X 0) ha,
        powerSeries_subst_subst_of_constantCoeff_zero lam (MvPowerSeries.constantCoeff_X 1) ha,
        MvPowerSeries.subst_X ha, MvPowerSeries.subst_X ha]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [hlog, hXs, Nat.cast_succ, map_add, map_one]
      ring
end ReciprocityTheory.ChartRestriction.L1
