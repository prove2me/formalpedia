-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.divBy_expand_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:46:15.359094+00:00
-- url     : https://prove2.me/submissions/96e7d364-af46-42d8-964f-efc951d71b1f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
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
variable {K : Type} [NormedField K] [IsUltrametricDist K]
section Ring
variable {ι : Type}
end Ring
section OneVar
private theorem coeff_subst_X_pow_eq_ite_dvd' (f : PowerSeries K) {k : ℕ} (hk : k ≠ 0) (m : ℕ) :
    coeff m (f.subst ((X : PowerSeries K) ^ k)) = if k ∣ m then coeff (m / k) f else 0 := by
  have ha : PowerSeries.HasSubst ((X : PowerSeries K) ^ k) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hk])
  rw [PowerSeries.coeff_subst' ha]
  simp only [← pow_mul, PowerSeries.coeff_X_pow]
  split_ifs with hd
  · obtain ⟨q, rfl⟩ := hd
    rw [finsum_eq_single _ q]
    · simp [Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero hk)]
    · intro d hd
      have : k * q ≠ k * d := fun h => hd (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) h).symm
      simp [this]
  · rw [finsum_eq_zero_of_forall_eq_zero]
    intro d
    have : m ≠ k * d := fun h => hd ⟨d, h⟩
    simp [this]
end OneVar
section Subst
variable {ι : Type}
end Subst
section Frob
variable {l : ℕ} {σ : K →+* K} {ι : Type}
end Frob
end ReciprocityTheory.ChartRestriction.L1
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (x : K) (n : ℕ) (hn : n ≠ 0) (f : PowerSeries K) :
    DivBy x (f.subst ((X : PowerSeries K) ^ n)) ↔ DivBy x f := by
  unfold DivBy
  constructor
  · intro h m
    have := h (n * m)
    rwa [coeff_subst_X_pow_eq_ite_dvd' f hn, if_pos (dvd_mul_right n m),
      Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hn)] at this
  · intro h m
    rw [coeff_subst_X_pow_eq_ite_dvd' f hn]
    split_ifs
    · exact h _
    · rw [norm_zero]
      exact norm_nonneg _
end ReciprocityTheory.ChartRestriction.L1
