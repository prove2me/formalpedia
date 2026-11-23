-- Prove2me | solution 1 for PI.AddIntG.Wk.mvsubst_mem_SerS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:29.225803+00:00
-- url     : https://prove2.me/submissions/70a0cfde-d913-4d68-aa1a-27b58708edc4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AddIntG PI.AddIntG.Wk
namespace PI.AddIntG.Wk
theorem _root_.solution {K : Type*} [CommRing K] (S : Subring K) {σ τ : Type*} [Finite σ]
    {a : σ → MvPowerSeries τ K} {f : MvPowerSeries σ K} (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (ha : ∀ i, a i ∈ SerS S τ) (hf : f ∈ SerS S σ) : MvPowerSeries.subst a f ∈ SerS S τ := by
  classical
  rw [mem_SerS] at hf ⊢
  intro e
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha0)]
  have hterm : ∀ d : σ →₀ ℕ,
      MvPowerSeries.coeff d f • MvPowerSeries.coeff e (d.prod fun s n => a s ^ n) ∈ S := by
    intro d
    rw [smul_eq_mul]
    refine S.mul_mem (hf d) ?_
    have hp : (d.prod fun s n => a s ^ n) ∈ SerS S τ :=
      Subring.prod_mem _ fun s _ => Subring.pow_mem _ (ha s) _
    exact (mem_SerS S _).1 hp e
  rw [finsum_def]
  split_ifs
  · exact Subring.sum_mem _ fun i _ => hterm _
  · exact S.zero_mem
end PI.AddIntG.Wk
