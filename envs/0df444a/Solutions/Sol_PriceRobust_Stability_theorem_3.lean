-- Prove2me | solution 1 for PriceRobust.Stability.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T00:46:59.240301+00:00
-- url     : https://prove2.me/submissions/abcf422b-bfaa-4079-a788-0ab5847b5e71

import Mathlib
import Definitions.Def_PriceRobust_Stability_Model
import Theorems.Thm_PriceRobust_Stability_theorem_2
import Theorems.Thm_PriceRobust_Stability_robust_br_componentwise_bound
import Theorems.Thm_PriceRobust_Stability_lam_nonneg_spectralRadius_lt_one
import Theorems.Thm_PriceRobust_Stability_absolute_norm_near_spectral_radius

open Matrix

namespace PRSThm3Aux

/-- Changing one coordinate of `v` to a value of no larger modulus does not increase an
absolute seminorm. -/
theorem update_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν : Seminorm ℝ (ι → ℝ)) (habs : ∀ x, ν x = ν (fun l => |x l|))
    (v : ι → ℝ) (k : ι) (c : ℝ) (hc : |c| ≤ |v k|) :
    ν (Function.update v k c) ≤ ν v := by
  by_cases hv : v k = 0
  · have hc0 : c = 0 := by
      rw [hv, abs_zero] at hc; exact abs_nonpos_iff.mp hc
    have : Function.update v k c = v := by
      rw [hc0, ← hv]; exact Function.update_eq_self k v
    rw [this]
  · set v' := Function.update v k (-(v k)) with hv'
    have hνv' : ν v' = ν v := by
      rw [habs v', habs v]
      congr 1
      funext l
      by_cases hl : l = k
      · subst hl; simp [hv']
      · simp [hv', Function.update_of_ne hl]
    set t : ℝ := (1 + c / v k) / 2 with ht
    have hratio : |c / v k| ≤ 1 := by
      rw [abs_div, div_le_one (abs_pos.mpr hv)]; exact hc
    have ht0 : 0 ≤ t := by
      have := (abs_le.mp hratio).1; rw [ht]; linarith
    have ht1 : t ≤ 1 := by
      have := (abs_le.mp hratio).2; rw [ht]; linarith
    have hdecomp : Function.update v k c = t • v + (1 - t) • v' := by
      funext l
      by_cases hl : l = k
      · subst hl
        simp only [Function.update_self, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hv']
        rw [ht]; field_simp; ring
      · simp [hv', Function.update_of_ne hl]; ring
    rw [hdecomp]
    calc ν (t • v + (1 - t) • v') ≤ ν (t • v) + ν ((1 - t) • v') := map_add_le_add ν _ _
      _ = t * ν v + (1 - t) * ν v := by
          rw [map_smul_eq_mul, map_smul_eq_mul, hνv', Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg ht0, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - t)]
      _ = ν v := by ring

/-- An absolute seminorm is monotone. -/
theorem mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν : Seminorm ℝ (ι → ℝ)) (habs : ∀ x, ν x = ν (fun l => |x l|))
    (x y : ι → ℝ) (hxy : ∀ l, |x l| ≤ |y l|) : ν x ≤ ν y := by
  have key : ∀ S : Finset ι, ν (S.piecewise x y) ≤ ν y := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert k S hk ih =>
      have : (insert k S).piecewise x y = Function.update (S.piecewise x y) k (x k) := by
        rw [Finset.piecewise_insert]
      rw [this]
      refine le_trans (update_le ν habs _ k (x k) ?_) ih
      rw [Finset.piecewise_eq_of_notMem _ _ _ hk]; exact hxy k
  have := key Finset.univ
  rwa [Finset.piecewise_univ] at this

/-- Each coordinate is controlled by an absolute seminorm. -/
theorem coord_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν : Seminorm ℝ (ι → ℝ)) (habs : ∀ x, ν x = ν (fun l => |x l|))
    (x : ι → ℝ) (l : ι) : |x l| * ν (Pi.single l 1) ≤ ν x := by
  have h1 : ν (Pi.single l (x l)) ≤ ν x := by
    apply mono ν habs
    intro m
    by_cases hm : m = l
    · subst hm; simp
    · simp [Pi.single_apply, hm]
  have h2 : (Pi.single l (x l) : ι → ℝ) = (x l) • (Pi.single l 1 : ι → ℝ) := by
    rw [← Pi.single_smul]; simp
  rw [h2, map_smul_eq_mul, Real.norm_eq_abs] at h1
  exact h1

end PRSThm3Aux

open PriceRobust.Stability PRSThm3Aux

theorem solution {ι F : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq F]
    (M : Market ι F) (hM : M.Standing) (w : ι → ℝ) (hw : ∀ l, 0 < w l)
    (w' : ι → ℝ) (hw' : M.IsCostProjection w w') :
    ∃ ν : Seminorm ℝ (ι → ℝ), (∀ x, ν x = 0 → x = 0) ∧
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧
      (∀ phat ptil qhat qtil : ι → ℝ, 0 ≤ phat → 0 ≤ ptil →
        M.IsRobustBR w phat qhat → M.IsRobustBR w ptil qtil →
        ν (qhat - qtil) ≤ γ * ν (phat - ptil)) ∧
      (∀ s : ℕ → ι → ℝ, 0 ≤ s 0 → (∀ n, M.IsRobustBR w (s n) (s (n + 1))) →
        (∀ n, ν (s n - M.pstar w') ≤ γ ^ n * ν (s 0 - M.pstar w')) ∧
        Filter.Tendsto s Filter.atTop (nhds (M.pstar w'))) := by
  obtain ⟨_hLnn, hρ⟩ := lam_nonneg_spectralRadius_lt_one M hM
  set ρ := spectralRadius ℂ (M.Lam.map (algebraMap ℝ ℂ)) with hρdef
  have hρtop : ρ ≠ ⊤ := ne_top_of_lt hρ
  set r := ρ.toReal with hr
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  have hr1 : r < 1 := by
    have := (ENNReal.toReal_lt_toReal hρtop ENNReal.one_ne_top).mpr hρ
    simpa using this
  have hρr : ρ = ENNReal.ofReal r := (ENNReal.ofReal_toReal hρtop).symm
  set ε : ℝ := (1 - r) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨ν, hνdef, habs, hbound⟩ := absolute_norm_near_spectral_radius M hM ε hε0
  set γ : ℝ := r + ε with hγ
  have hγ0 : 0 < γ := by rw [hγ]; linarith
  have hγ1 : γ < 1 := by rw [hγ, hε]; linarith
  -- ν (Λ x) ≤ γ ν x
  have hLam : ∀ x, ν (M.Lam *ᵥ x) ≤ γ * ν x := by
    intro x
    have h := hbound x
    rw [← hρdef, hρr, ← ENNReal.ofReal_add hr0 hε0.le, ← ENNReal.ofReal_mul (by linarith)] at h
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hγ0.le (apply_nonneg ν x))).mp h
  -- contraction
  have hcontr : ∀ phat ptil qhat qtil : ι → ℝ, 0 ≤ phat → 0 ≤ ptil →
      M.IsRobustBR w phat qhat → M.IsRobustBR w ptil qtil →
      ν (qhat - qtil) ≤ γ * ν (phat - ptil) := by
    intro phat ptil qhat qtil hp1 hp2 hq1 hq2
    have hcw := robust_br_componentwise_bound M hM w hw phat ptil qhat qtil hp1 hp2 hq1 hq2
    have h1 : ν (qhat - qtil) ≤ ν (M.Lam *ᵥ (fun m => |phat m - ptil m|)) := by
      apply mono ν habs
      intro l
      simp only [Pi.sub_apply]
      exact le_trans (hcw l) (le_abs_self _)
    have h2 : ν (fun m => |phat m - ptil m|) = ν (phat - ptil) := by
      rw [habs (phat - ptil)]; rfl
    calc ν (qhat - qtil) ≤ ν (M.Lam *ᵥ (fun m => |phat m - ptil m|)) := h1
      _ ≤ γ * ν (fun m => |phat m - ptil m|) := hLam _
      _ = γ * ν (phat - ptil) := by rw [h2]
  refine ⟨ν, hνdef, γ, hγ0, hγ1, hcontr, ?_⟩
  intro s hs0 hs
  -- robust best responses are nonnegative
  have hBRnn : ∀ p q, M.IsRobustBR w p q → 0 ≤ q := by
    intro p q hpq l
    exact ((hpq (M.firm l)).1 l rfl).1
  have hfix := theorem_2 M hM w hw w' hw'
  have hpnn : 0 ≤ M.pstar w' := hBRnn _ _ hfix
  have hsnn : ∀ n, 0 ≤ s n := by
    intro n
    cases n with
    | zero => exact hs0
    | succ n => exact hBRnn _ _ (hs n)
  have hgeo : ∀ n, ν (s n - M.pstar w') ≤ γ ^ n * ν (s 0 - M.pstar w') := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc ν (s (n + 1) - M.pstar w') ≤ γ * ν (s n - M.pstar w') :=
            hcontr _ _ _ _ (hsnn n) hpnn (hs n) hfix
        _ ≤ γ * (γ ^ n * ν (s 0 - M.pstar w')) :=
            mul_le_mul_of_nonneg_left ih hγ0.le
        _ = γ ^ (n + 1) * ν (s 0 - M.pstar w') := by ring
  refine ⟨hgeo, ?_⟩
  rw [tendsto_pi_nhds]
  intro l
  have hel : 0 < ν (Pi.single l 1) := by
    rcases (apply_nonneg ν (Pi.single l (1:ℝ))).lt_or_eq with h | h
    · exact h
    · exfalso
      have := hνdef _ h.symm
      have h' := congrFun this l
      simp at h'
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (g := fun n =>
    γ ^ n * (ν (s 0 - M.pstar w') / ν (Pi.single l 1))) ?_ ?_
  · intro n
    rw [Real.norm_eq_abs]
    have hc := coord_le ν habs (s n - M.pstar w') l
    simp only [Pi.sub_apply] at hc
    rw [← mul_div_assoc, le_div_iff₀ hel]
    exact le_trans hc (hgeo n)
  · have := (tendsto_pow_atTop_nhds_zero_of_lt_one hγ0.le hγ1).mul_const
      (ν (s 0 - M.pstar w') / ν (Pi.single l 1))
    simpa using this
