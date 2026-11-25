-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.lg_agree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:44:47.904838+00:00
-- url     : https://prove2.me/submissions/cf19854d-6c94-4de2-9301-ecb2580973f9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_LgCurvePcurve
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CoeffLgPcurveTop
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_coeff_lg_pcurve
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_ptx_rel


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb
theorem _root_.solution (G : LogFGL v d) {p : ℕ} (hp : p.Prime) {γ : Fin d → Fin d → PowerSeries C}
    (hγ : ∀ a, IsCurve v (γ a)) (hγt : ∀ b, G.IsPTypical p (γ b)) (hdet : v (tmat γ).det = 0)
    (ga : Fin d → PowerSeries C) (hga : G.IsPTypical p ga) (n : ℕ)
    (hx : ∀ s < n, ∀ b, IsIntV v (ptx G p γ ga s b)) :
    ∀ a, ∀ j < p ^ n, PowerSeries.coeff j (G.lgCurve ga a) =
      PowerSeries.coeff j (G.lgCurve (pcurve G p γ (ptx G p γ ga) n) a) := by
  intro a j hj
  rw [coeff_lg_pcurve G hp.ne_zero hγ _ n hx a j]
  by_cases hpow : ∃ m, j = p ^ m
  · obtain ⟨m, rfl⟩ := hpow
    have hmn : m < n := by
      by_contra h
      push_neg at h
      exact absurd hj (not_lt.mpr (Nat.pow_le_pow_right hp.pos h))
    have hrel := congrFun (ptx_rel G p hγ hdet ga m) a
    change G.lc p ga m a = _
    rw [hrel]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.sum_range_add_sum_Ico _ (show m + 1 ≤ n by omega)]
    have hzero : ∑ s ∈ Finset.Ico (m + 1) n, ∑ b, (if p ^ s ∣ p ^ m then
        ptx G p γ ga s b ^ (p ^ m / p ^ s) * PowerSeries.coeff (p ^ m / p ^ s) (G.lgCurve (γ b) a)
        else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro s hs
      have hs' : m < s := by
        rw [Finset.mem_Ico] at hs
        omega
      apply Finset.sum_eq_zero
      intro b _
      rw [if_neg]
      intro hd
      have hle : s ≤ m := by
        first
        | exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hd
        | exact (Nat.pow_dvd_pow_iff_le_right' ).mp hd
      omega
    rw [hzero, add_zero]
    apply Finset.sum_congr rfl
    intro s hs
    have hsm : s ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    apply Finset.sum_congr rfl
    intro b _
    rw [if_pos (pow_dvd_pow p hsm), Nat.pow_div hsm hp.pos]
    rfl
  · push_neg at hpow
    rw [hga a j hpow]
    symm
    apply Finset.sum_eq_zero
    intro s _
    apply Finset.sum_eq_zero
    intro b _
    split_ifs with hd
    · obtain ⟨k, hk⟩ := hd
      have hk' : j / p ^ s = k := by
        rw [hk, Nat.mul_div_cancel_left _ (pow_pos hp.pos s)]
      have hnp : ∀ m', k ≠ p ^ m' := by
        intro m' hm'
        apply hpow (s + m')
        rw [hk, hm', pow_add]
      rw [hk', hγt b a k hnp, mul_zero]
    · rfl
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
