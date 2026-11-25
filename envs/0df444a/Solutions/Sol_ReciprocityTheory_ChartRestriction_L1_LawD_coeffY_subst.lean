-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.LawD.coeffY_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:42:49.523899+00:00
-- url     : https://prove2.me/submissions/d6c4fe57-9d32-45c5-8822-8c5637e25cb6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_partialYAtZero_subst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_LawD_evalYZero_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
section Ev
variable {R : Type} [CommRing R]
end Ev
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}
variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K}
private theorem powerSeries_subst_X_self_commRing {S : Type} [CommRing S] (t : PowerSeries S) :
    t.subst (X : PowerSeries S) = t := by
  ext n
  rw [PowerSeries.coeff_subst' (HasSubst.of_constantCoeff_zero constantCoeff_X), finsum_eq_single _ n]
  · simp
  · intro d hd
    simp [coeff_X_pow, Ne.symm hd]
end ReciprocityTheory.ChartRestriction.L1
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}
variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K}
namespace ReciprocityTheory.ChartRestriction.L1
namespace LawD
theorem _root_.solution (h : LawD lam Φ) (D : PowerSeries K) :
    d2 (D.subst Φ) = derivative K D * d2 Φ := by
  rw [partialYAtZero_subst D h.Φ0, h.evalYZero_eq, powerSeries_subst_X_self_commRing]
end LawD
end ReciprocityTheory.ChartRestriction.L1
