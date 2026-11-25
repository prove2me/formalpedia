-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.evalYZero_atX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:35:32.484007+00:00
-- url     : https://prove2.me/submissions/d74122b1-7713-493d-9c8c-e69b589c2a87

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_coeff_evalYZero
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
private theorem mvPowerSeries_coeff_subst_X_eq_ite_single {S : Type} [CommRing S] {ι : Type} [DecidableEq ι] (i : ι) (f : PowerSeries S)
    (e : ι →₀ ℕ) :
    MvPowerSeries.coeff e (f.subst (MvPowerSeries.X i : MvPowerSeries ι S)) =
      if e = Finsupp.single i (e i) then coeff (e i) f else 0 := by
  have ha : HasSubst (MvPowerSeries.X i : MvPowerSeries ι S) :=
    HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  rw [PowerSeries.coeff_subst ha]
  simp only [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  split_ifs with h
  · rw [finsum_eq_single _ (e i)]
    · rw [if_pos h]
    · intro d hd
      rw [if_neg]
      intro he
      exact hd (by rw [he, Finsupp.single_eq_same])
  · rw [finsum_eq_zero_of_forall_eq_zero]
    intro d
    rw [if_neg]
    intro he
    exact h (by rw [he, Finsupp.single_eq_same])
end Ev
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}
variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K}
end ReciprocityTheory.ChartRestriction.L1
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {R : Type} [CommRing R]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (φ : PowerSeries R) : ev0 (atX φ) = φ := by
  ext n
  rw [coeff_evalYZero]
  unfold atX
  rw [mvPowerSeries_coeff_subst_X_eq_ite_single]
  simp
end ReciprocityTheory.ChartRestriction.L1
