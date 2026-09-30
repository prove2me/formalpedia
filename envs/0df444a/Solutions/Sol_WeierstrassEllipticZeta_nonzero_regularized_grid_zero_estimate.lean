-- Prove2me | solution 1 for WeierstrassEllipticZeta.nonzero_regularized_grid_zero_estimate
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T13:37:19.405003+00:00
-- url     : https://prove2.me/submissions/457bc331-8dbb-429e-9776-99961366996f

import Theorems.Thm_WeierstrassEllipticZeta_cleared_auxiliary_polynomial_presentation
import Theorems.Thm_WeierstrassEllipticZeta_polynomial_regularized_grid_zero_estimate
import Theorems.Thm_WeierstrassEllipticZeta_hasDerivAt_weierstrassZeta
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.FinCases
import Definitions.Def_WeierstrassEllipticZeta_AuxiliaryGrids
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

open WeierstrassEllipticZeta
open Filter
open scoped Topology

theorem solution
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (D : EllipticSigmaDifferentialData L) :
    ∃ C : ℝ, 0 < C ∧ ∀ m l s q T : ℕ,
      1 ≤ m → 1 ≤ l → 1 ≤ s → 1 ≤ q → s ≤ q → l ≤ m → 3 ≤ T →
      3 * C * max ((m : ℝ) * (15 * l) ^ 2) ((q : ℝ) * (15 * l) ^ 2) <
        (T : ℝ) * (s : ℝ) ^ 2 * q →
      ∀ (c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ) (G : ℂ → ℂ),
        AnalyticOnNhd ℂ G Set.univ →
        (∀ w : ℂ, w ∉ L.lattice → w + u₁ / 2 ∉ L.lattice →
          G w = D.sigma w ^ (15 * l) *
            (2 * (L.weierstrassP (u₁ / 2) - L.weierstrassP w)) ^ (3 * l) *
            (∑ i, c i * (w + u₁ / 2) ^ i.1.val *
              L.weierstrassP (w + u₁ / 2) ^ i.2.1.val *
              weierstrassZeta L (w + u₁ / 2) ^ i.2.2.val)) →
        G ≠ 0 → ∃ v ∈ auxiliaryGrid u₁ u₂ ω ![3 * s, 3 * s, 3 * q],
          ∃ n : ℕ, n ≤ T ∧ iteratedDeriv n G v ≠ 0 := by
  classical
  obtain ⟨C, hC, hzero⟩ := polynomial_regularized_grid_zero_estimate L ω u₁ u₂ h_grid D
  refine ⟨C, hC, ?_⟩
  intro m l s q T hm hl hs hq hsq hlm hT hineq c G hG hG_value hG_ne
  have hbase : u₁ / 2 ∉ L.lattice := by
    simpa [integerGridPoint] using h_grid.shifted_regular (fun _ => 0)
  obtain ⟨P, hP, hP_value⟩ := cleared_auxiliary_polynomial_presentation L (u₁ / 2) hbase m l c
  apply hzero m l s q T hm hl hs hq hsq hlm hT hineq P G hP hG ?_ hG_ne
  intro z hz
  let f : ℂ → Fin 4 → ℂ := fun w =>
    ![w, L.weierstrassP w, L.derivWeierstrassP w, weierstrassZeta L w]
  let R : ℂ → ℂ := fun w => D.sigma w ^ (15 * l) * MvPolynomial.eval (f w) P
  have hf : ContinuousAt f z := by
    apply continuousAt_pi.mpr
    intro i
    fin_cases i
    · change ContinuousAt id z
      exact continuousAt_id
    · simpa [f] using (L.analyticOnNhd_weierstrassP z hz).continuousAt
    · simpa [f] using (L.analyticOnNhd_derivWeierstrassP z hz).continuousAt
    · simpa [f] using (hasDerivAt_weierstrassZeta L z hz).continuousAt
  have hR : ContinuousAt R z :=
    (D.entire.continuous.continuousAt.pow _).mul
      ((MvPolynomial.continuous_eval P).continuousAt.comp hf)
  have hpunct : G =ᶠ[𝓝[≠] z] R := by
    have hreg : ∀ᶠ w in 𝓝 z, w ∉ L.lattice :=
      L.isClosed_lattice.isOpen_compl.mem_nhds hz
    have hshift : ∀ᶠ w in 𝓝 z,
        w + u₁ / 2 ∈ ((L.lattice : Set ℂ) \ {z + u₁ / 2})ᶜ :=
      (continuousAt_id.add continuousAt_const).eventually
        (L.compl_lattice_sdiff_singleton_mem_nhds (z + u₁ / 2))
    filter_upwards [hreg.filter_mono nhdsWithin_le_nhds,
      hshift.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw hwshift hwz
    have hwv : w + u₁ / 2 ∉ L.lattice := by
      intro hwl
      exact hwshift ⟨hwl, fun he => hwz (add_right_cancel he)⟩
    dsimp only [R, f]
    rw [hP_value w hw hwv, hG_value w hw hwv, mul_assoc]
  exact ((hG z (Set.mem_univ z)).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    hR |>.mp hpunct).eq_of_nhds
