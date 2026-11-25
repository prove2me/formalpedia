-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.LawD.subst_of_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:34:13.14922+00:00
-- url     : https://prove2.me/submissions/2ac0e644-e206-4c28-8f22-c889279716e1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_DivByPartialYAtZeroSubstAtXAtY
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_SubstOfLog
import Theorems.Thm_Formalism_G_LogP_hb0
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_psubst_injective
import Theorems.Thm_Formalism_G_LogP_psubst_subst


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
namespace LawD
theorem _root_.solution (h : LawD lam Φ) {e : PowerSeries K} {c : K} (he0 : constantCoeff e = 0)
    (hlog : lam.subst e = C c * lam) : e.subst Φ = Φ.subst ![atX e, atY e] := by
  have hes : PowerSeries.HasSubst e := PowerSeries.HasSubst.of_constantCoeff_zero' he0
  have hΦs : PowerSeries.HasSubst Φ := PowerSeries.HasSubst.of_constantCoeff_zero h.Φ0
  have hlog' : lam.subst e = c • lam := by rw [hlog, smul_eq_C_mul]
  have hX : ∀ i : Fin 2, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) :=
    fun i => PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  have hx0 : MvPowerSeries.constantCoeff (atX e) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X _) _ he0
  have hy0 : MvPowerSeries.constantCoeff (atY e) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X _) _ he0
  have hb : MvPowerSeries.HasSubst ![atX e, atY e] := Formalism.G.LogP.hs2 hx0 hy0
  have hb0 : ∀ i, MvPowerSeries.constantCoeff (![atX e, atY e] i) = 0 := by
    intro i; fin_cases i <;> simpa
  refine Formalism.G.LogP.psubst_injective h.lam0 h.lam1
    (PowerSeries.constantCoeff_subst_eq_zero h.Φ0 _ he0)
    (MvPowerSeries.constantCoeff_subst_eq_zero hb hb0 h.Φ0) ?_
  rw [← PowerSeries.subst_comp_subst_apply hes hΦs, hlog', PowerSeries.subst_smul hΦs, h.log,
    ← Formalism.G.LogP.psubst_subst lam h.Φ0 hb, h.log, MvPowerSeries.subst_add hb,
    Formalism.G.LogP.psubst_subst lam (MvPowerSeries.constantCoeff_X _) hb,
    Formalism.G.LogP.psubst_subst lam (MvPowerSeries.constantCoeff_X _) hb,
    MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb]
  show _ = lam.subst (e.subst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K))
    + lam.subst (e.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K))
  rw [← PowerSeries.subst_comp_subst_apply hes (hX 0), ← PowerSeries.subst_comp_subst_apply hes (hX 1),
    hlog', PowerSeries.subst_smul (hX 0), PowerSeries.subst_smul (hX 1), smul_add]
end LawD
end ReciprocityTheory.ChartRestriction.L1
