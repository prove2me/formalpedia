-- Prove2me | solution 1 for PI.OrbShared.Tri.coeff_P_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:15:17.048884+00:00
-- url     : https://prove2.me/submissions/465799b0-9301-4286-993d-b9a719990383

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrbitPowerSeriesCoefficients_SolvableEquivalenceOfBaseChange
import Theorems.Thm_PI_OrbShared_Tri_ord_prod_sub
import Theorems.Thm_PI_OrbShared_Tri_prod_CX
import Theorems.Thm_PI_OrbShared_Tri_IsTri_order_one
import Theorems.Thm_PI_OrbShared_Tri_IsTri_order_sub

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
open PI PI.OrbShared PI.OrbShared.Tri
open MvPowerSeries Finsupp
variable {K : Type*} [Field K] {σ : Type*} [Finite σ]
variable {c : K} {a : σ → MvPowerSeries σ K}
namespace PI.OrbShared.Tri
theorem _root_.solution (ha : IsTri c a) (d e : σ →₀ ℕ) (he : e.degree ≤ d.degree) :
    coeff e (P a d) = if e = d then c ^ d.degree else 0 := by
  have hX : ∀ v, 1 ≤ (C c * X v : MvPowerSeries σ K).order := fun v =>
    one_le_order_iff_constCoeff_eq_zero.mpr (by simp)
  have h := (ord_prod_sub d.support (fun v => C c * X v) a d hX ha.order_one ha.order_sub).2
  have h0 : coeff e (P a d - d.prod fun s e => (C c * X s : MvPowerSeries σ K) ^ e) = 0 := by
    apply coeff_of_lt_order
    refine lt_of_lt_of_le ?_ h
    have : (∑ i ∈ d.support, d i) = d.degree := rfl
    rw [this]
    exact_mod_cast Nat.lt_succ_of_le he
  rw [map_sub, prod_CX, coeff_monomial, sub_eq_zero] at h0
  exact h0
end PI.OrbShared.Tri
