-- Prove2me | solution 1 for WeierstrassEllipticZeta.regular_grid_polynomial_zero_estimate
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T02:11:06.983135+00:00
-- url     : https://prove2.me/submissions/af285aff-aead-4a6f-aaf0-b48c6951d5fc

import Theorems.Thm_WeierstrassEllipticZeta_regularized_nonzero_derivative_transfer
import Theorems.Thm_WeierstrassEllipticZeta_regular_grid_sigma_zero_estimate
import Theorems.Thm_WeierstrassEllipticZeta_hasDerivAt_weierstrassZeta
import Theorems.Thm_WeierstrassEllipticZeta_exists_elliptic_sigma_differential_data
import Theorems.Thm_WeierstrassEllipticZeta_sigma_regularized_coordinates_entire
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Definitions.Def_WeierstrassEllipticZeta_AuxiliaryGrids
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

open WeierstrassEllipticZeta

theorem solution
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ m l s q T : ℕ,
      1 ≤ m → 1 ≤ l → 1 ≤ s → 1 ≤ q → s ≤ q → l ≤ m → 3 ≤ T →
      3 * C * max ((m : ℝ) * (15 * l) ^ 2) ((q : ℝ) * (15 * l) ^ 2) <
        (T : ℝ) * (s : ℝ) ^ 2 * q →
      ∀ c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ,
        c ≠ 0 → ∃ v ∈ auxiliaryGrid u₁ u₂ ω ![3 * s, 3 * s, 3 * q],
          ∃ n : ℕ, n ≤ T + 6 * l ∧
            iteratedDeriv n (fun w => ∑ i, c i * w ^ i.1.val *
              L.weierstrassP w ^ i.2.1.val * weierstrassZeta L w ^ i.2.2.val)
                (u₁ / 2 + v) ≠ 0 := by
  classical
  obtain ⟨D⟩ := exists_elliptic_sigma_differential_data L
  have hζ := hasDerivAt_weierstrassZeta L
  obtain ⟨S, hS, hS_value, _⟩ := sigma_regularized_coordinates_entire L D hζ
  obtain ⟨C, hC, hzero⟩ := regular_grid_sigma_zero_estimate L ω u₁ u₂ h_grid D
  refine ⟨C, hC, ?_⟩
  intro m l s q T hm hl hs hq hsq hlm hT hineq c hc
  obtain ⟨G, hG, hG_value, v, hv, t, ht, hnonzero⟩ :=
    hzero m l s q T hm hl hs hq hsq hlm hT hineq c hc
  let F₀ : ℂ → ℂ := fun w => ∑ i, c i * w ^ i.1.val *
    L.weierstrassP w ^ i.2.1.val * weierstrassZeta L w ^ i.2.2.val
  let F : ℂ → ℂ := fun w => F₀ (w + u₁ / 2)
  have hZ : AnalyticOnNhd ℂ (weierstrassZeta L) L.latticeᶜ :=
    (show DifferentiableOn ℂ (weierstrassZeta L) L.latticeᶜ from
      fun z hz => (hζ z hz).differentiableAt.differentiableWithinAt).analyticOnNhd
        L.isClosed_lattice.isOpen_compl
  have hF₀ (w : ℂ) (hw : w ∉ L.lattice) : AnalyticAt ℂ F₀ w := by
    apply Finset.analyticAt_fun_sum
    intro i hi
    exact (((analyticAt_const.mul (analyticAt_id.pow _)).mul
      ((L.analyticOnNhd_weierstrassP w hw).pow _)).mul ((hZ w hw).pow _))
  have hF : AnalyticOnNhd ℂ F {w : ℂ | w + u₁ / 2 ∉ L.lattice} := by
    intro w hw
    exact (hF₀ _ hw).comp (f := fun w : ℂ => w + u₁ / 2)
      (show AnalyticAt ℂ (fun w : ℂ => w + u₁ / 2) w from
        analyticAt_id.add analyticAt_const)
  have hσ : AnalyticOnNhd ℂ D.sigma Set.univ := fun w _ => D.entire.analyticAt w
  have hS₁ : ∀ w : ℂ, w ∉ L.lattice → S 1 w = D.sigma w ^ 2 * L.weierstrassP w := by
    intro w hw
    simpa [ellipticPoleCoordinates] using hS_value w hw 1
  have hvreg : v + u₁ / 2 ∉ L.lattice :=
    h_grid.shifted_grid_regular ![3 * s, 3 * s, 3 * q] (v + u₁ / 2)
      (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
  obtain ⟨n, hn, hFn⟩ := regularized_nonzero_derivative_transfer L (u₁ / 2)
    F D.sigma (S 1) G (15 * l) l (by omega) hF hσ (hS 1) hG hS₁ hG_value
    v hvreg t hnonzero
  refine ⟨v, hv, n, hn.trans (ht.trans (Nat.le_add_right T (6 * l))), ?_⟩
  simpa only [F, iteratedDeriv_comp_add_const, add_comm v (u₁ / 2)] using hFn
