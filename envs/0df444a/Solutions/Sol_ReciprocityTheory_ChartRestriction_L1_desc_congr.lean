-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.desc_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:37:57.411578+00:00
-- url     : https://prove2.me/submissions/7722690e-a1a8-413e-92fe-e7f25f80196e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_natCast_of_coprime

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
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}
private theorem coeff_subst_X_pow_lemma (f : PowerSeries K) {k : ℕ} (hk : k ≠ 0) (m : ℕ) :
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
end ReciprocityTheory.ChartRestriction.L1
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) (D : PowerSeries K)
    (hD : DivBy (l : K) (derivative K D)) :
    DivBy (l : K) (D - (desc l D).subst ((X : PowerSeries K) ^ l)) ∧
      IntegralPS (derivative K (desc l D)) := by
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne_zero
  have hlpos : 0 < ‖(l : K)‖ := norm_pos_iff.mpr hl0
  have hD' : ∀ n, ‖coeff n (derivative K D)‖ ≤ ‖(l : K)‖ := hD
  have hD2 : ∀ m, ‖coeff (m + 1) D‖ * ‖((m : K) + 1)‖ ≤ ‖(l : K)‖ := by
    intro m
    have h := hD' m
    rwa [PowerSeries.coeff_derivative, norm_mul] at h
  refine ⟨?_, ?_⟩
  · intro m
    rw [map_sub, coeff_subst_X_pow_lemma _ hl.ne_zero]
    split_ifs with hd
    · obtain ⟨q, rfl⟩ := hd
      rw [desc, PowerSeries.coeff_mk, Nat.mul_div_cancel_left q hl.pos, sub_self, norm_zero]
      exact norm_nonneg _
    · rw [sub_zero]
      have hm0 : m ≠ 0 := fun h => hd (h ▸ dvd_zero l)
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have h1 := hD2 m'
      have hu : ‖((m' : K) + 1)‖ = 1 := by
        have h2 := norm_natCast_of_coprime hl hl1 (m' + 1) hd
        push_cast at h2
        exact h2
      rwa [hu, mul_one] at h1
  · intro m
    rw [PowerSeries.coeff_derivative, desc, PowerSeries.coeff_mk, norm_mul]
    have e : l * (m + 1) - 1 + 1 = l * (m + 1) :=
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hl.ne_zero (Nat.succ_ne_zero m)))
    have e2 : ((l * (m + 1) - 1 : ℕ) : K) + 1 = (l : K) * ((m : K) + 1) := by
      rw [← Nat.cast_add_one, e]
      push_cast
      ring
    have h1 := hD2 (l * (m + 1) - 1)
    rw [e2, e, norm_mul] at h1
    have h2 : ‖(l : K)‖ * (‖coeff (l * (m + 1)) D‖ * ‖((m : K) + 1)‖) ≤ ‖(l : K)‖ * 1 := by
      linarith [h1]
    exact le_of_mul_le_mul_left h2 hlpos
end ReciprocityTheory.ChartRestriction.L1
