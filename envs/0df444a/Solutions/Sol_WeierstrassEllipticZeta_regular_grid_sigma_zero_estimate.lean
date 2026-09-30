-- Prove2me | solution 1 for WeierstrassEllipticZeta.regular_grid_sigma_zero_estimate
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T11:56:34.829123+00:00
-- url     : https://prove2.me/submissions/1f65c24d-d8cb-40ec-9465-d90ebb54bc59

import Theorems.Thm_WeierstrassEllipticZeta_regularization_preserves_nonvanishing
import Theorems.Thm_WeierstrassEllipticZeta_auxiliary_function_nonvanishing
import Theorems.Thm_WeierstrassEllipticZeta_nonzero_regularized_grid_zero_estimate
import Theorems.Thm_WeierstrassEllipticZeta_hasDerivAt_weierstrassZeta
import Theorems.Thm_WeierstrassEllipticZeta_zeta_addition_formula
import Theorems.Thm_WeierstrassEllipticZeta_wp_addition_formula
import Theorems.Thm_WeierstrassEllipticZeta_sigma_addition_from_differential
import Theorems.Thm_WeierstrassEllipticZeta_sigma_regularized_coordinates_entire
import Theorems.Thm_WeierstrassEllipticZeta_cleared_addition_entire_growth_weighted
import Mathlib.Tactic.Ring
import Definitions.Def_WeierstrassEllipticZeta_AuxiliaryGrids
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

open WeierstrassEllipticZeta

theorem solution
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (D : EllipticSigmaDifferentialData L) :
    ∃ C : ℝ, 0 < C ∧ ∀ m l s q T : ℕ,
      1 ≤ m → 1 ≤ l → 1 ≤ s → 1 ≤ q → s ≤ q → l ≤ m → 3 ≤ T →
      3 * C * max ((m : ℝ) * (15 * l) ^ 2) ((q : ℝ) * (15 * l) ^ 2) <
        (T : ℝ) * (s : ℝ) ^ 2 * q →
      ∀ c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ,
        c ≠ 0 → ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G Set.univ ∧
          (∀ w : ℂ, w ∉ L.lattice → w + u₁ / 2 ∉ L.lattice →
            G w = D.sigma w ^ (15 * l) *
              (2 * (L.weierstrassP (u₁ / 2) - L.weierstrassP w)) ^ (3 * l) *
              (∑ i, c i * (w + u₁ / 2) ^ i.1.val *
                L.weierstrassP (w + u₁ / 2) ^ i.2.1.val *
                weierstrassZeta L (w + u₁ / 2) ^ i.2.2.val)) ∧
          ∃ v ∈ auxiliaryGrid u₁ u₂ ω ![3 * s, 3 * s, 3 * q],
            ∃ n : ℕ, n ≤ T ∧ iteratedDeriv n G v ≠ 0 := by
  classical
  have hζ := hasDerivAt_weierstrassZeta L
  have hZ := zeta_addition_formula L
  have hP := wp_addition_formula L
  have hσne := (sigma_addition_from_differential L D hζ hZ).1
  have hσ : AnalyticOnNhd ℂ D.sigma Set.univ := fun z _ => D.entire.analyticAt z
  obtain ⟨S, hS, hS_value, _⟩ := sigma_regularized_coordinates_entire L D hζ
  have hbase : u₁ / 2 ∉ L.lattice := by
    simpa [integerGridPoint] using h_grid.shifted_regular (fun _ => 0)
  obtain ⟨C, hC, hzero⟩ := nonzero_regularized_grid_zero_estimate L ω u₁ u₂ h_grid D
  refine ⟨C, hC, ?_⟩
  intro m l s q T hm hl hs hq hsq hlm hT hineq c hc
  let F₀ : ℂ → ℂ := fun w => ∑ i, c i * w ^ i.1.val *
    L.weierstrassP w ^ i.2.1.val * weierstrassZeta L w ^ i.2.2.val
  let F : ℂ → ℂ := fun w => F₀ (w + u₁ / 2)
  have hZanalytic : AnalyticOnNhd ℂ (weierstrassZeta L) L.latticeᶜ :=
    (show DifferentiableOn ℂ (weierstrassZeta L) L.latticeᶜ from
      fun z hz => (hζ z hz).differentiableAt.differentiableWithinAt).analyticOnNhd
        L.isClosed_lattice.isOpen_compl
  have hF₀ (w : ℂ) (hw : w ∉ L.lattice) : AnalyticAt ℂ F₀ w := by
    apply Finset.analyticAt_fun_sum
    intro i hi
    exact (((analyticAt_const.mul (analyticAt_id.pow _)).mul
      ((L.analyticOnNhd_weierstrassP w hw).pow _)).mul ((hZanalytic w hw).pow _))
  have hF : ∀ w : ℂ, w + u₁ / 2 ∉ L.lattice → ContinuousAt F w := by
    intro w hw
    exact ((hF₀ _ hw).comp (f := fun w : ℂ => w + u₁ / 2)
      (show AnalyticAt ℂ (fun w : ℂ => w + u₁ / 2) w from
        analyticAt_id.add analyticAt_const)).continuousAt
  obtain ⟨G, hG, hG_value, _⟩ := cleared_addition_entire_growth_weighted
    L hZ hP D.sigma S hσ hS hS_value (u₁ / 2) hbase c
    (fun i => i.1.val) (fun i => i.2.1.val) (fun i => i.2.2.val) m l
    (fun i => by have := i.1.isLt; omega)
    (fun i => by have := i.2.1.isLt; omega)
    (fun i => by have := i.2.2.isLt; omega)
  have hGreg (w : ℂ) (hw : w ∉ L.lattice) (hwv : w + u₁ / 2 ∉ L.lattice) :
      G w = D.sigma w ^ (15 * l) *
        (2 * (L.weierstrassP (u₁ / 2) - L.weierstrassP w)) ^ (3 * l) * F w := by
    rw [hG_value w hw hwv, mul_assoc]
    congr 1
    dsimp only [F, F₀]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [clearedAdditionMonomial]
    ring
  obtain ⟨w, hw, hFw⟩ := auxiliary_function_nonvanishing L m l c hc
  have hFne : ∃ z : ℂ, z + u₁ / 2 ∉ L.lattice ∧ F z ≠ 0 := by
    refine ⟨w - u₁ / 2, ?_, ?_⟩
    · simpa only [sub_add_cancel] using hw
    · simpa only [F, F₀, sub_add_cancel] using hFw
  have hGne := regularization_preserves_nonvanishing L (u₁ / 2) F D.sigma G
    (15 * l) l hF hσne hGreg hFne
  exact ⟨G, hG, hGreg, hzero m l s q T hm hl hs hq hsq hlm hT hineq c G hG hGreg hGne⟩
