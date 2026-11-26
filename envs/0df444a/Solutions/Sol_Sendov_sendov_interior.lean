-- Prove2me | solution 1 for Sendov.sendov_interior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:32:43.486622+00:00
-- url     : https://prove2.me/submissions/cbac048c-61a6-4790-a716-d93853e2e750

import Definitions.Def_Sendov_Analytic_OriginExact
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_LowDegree
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Counterexample_Factor
import Definitions.Def_Sendov_Reduction_Main
import Definitions.Def_Sendov_Interior
import Theorems.Thm_Sendov_Fprod_zero
import Theorems.Thm_Sendov_centroid_identity
import Theorems.Thm_Sendov_exists_crit_multiset
import Theorems.Thm_Sendov_exists_root_multiset
import Theorems.Thm_Sendov_first_origin_identity
import Theorems.Thm_Sendov_gg0_length
import Theorems.Thm_Sendov_gg1_length
import Theorems.Thm_Sendov_gg2_length
import Theorems.Thm_Sendov_l1_cons
import Theorems.Thm_Sendov_l1_nil
import Theorems.Thm_Sendov_l1row_cons
import Theorems.Thm_Sendov_l1row_nil
import Theorems.Thm_Sendov_low_degree_contradiction
import Theorems.Thm_Sendov_npev_cons
import Theorems.Thm_Sendov_npev_nil
import Theorems.Thm_Sendov_one_le_integral_Ppolar
import Theorems.Thm_Sendov_one_le_integral_prod_norm
import Theorems.Thm_Sendov_origin_exact
import Theorems.Thm_Sendov_pevZ_cons
import Theorems.Thm_Sendov_pevZ_nil
import Theorems.Thm_Sendov_pev_cons
import Theorems.Thm_Sendov_pev_nil
import Theorems.Thm_Sendov_polar_identity
import Theorems.Thm_Sendov_polar_origin_incompatible
import Theorems.Thm_Sendov_prod_sub_mul_prod
import Theorems.Thm_Sendov_qrow_length
import Theorems.Thm_Sendov_rev_cons
import Theorems.Thm_Sendov_rev_nil
import Theorems.Thm_Sendov_rowZ_cons
import Theorems.Thm_Sendov_rowZ_length
import Theorems.Thm_Sendov_rowZ_nil
import Theorems.Thm_Sendov_rscale_length
import Theorems.Thm_Sendov_second_origin_identity
import Theorems.Thm_Sendov_sumEraseProdC_zero
import Theorems.Thm_Sendov_sumEraseProd_zero
import Theorems.Thm_Sendov_unpackN_succ
import Theorems.Thm_Sendov_unpackN_zero
import Theorems.Thm_Sendov_unpackZ_succ
import Theorems.Thm_Sendov_unpackZ_zero
import Theorems.Thm_Sendov_wsumZ_cons
import Theorems.Thm_Sendov_wsumZ_nil
import Theorems.Thm_Sendov_wsum_cons
import Theorems.Thm_Sendov_wsum_nil
import Theorems.Thm_Sendov_xy_bounds
attribute [local simp] Sendov.Fprod_zero
attribute [local simp] Sendov.gg0_length
attribute [local simp] Sendov.gg1_length
attribute [local simp] Sendov.gg2_length
attribute [local simp] Sendov.l1_cons
attribute [local simp] Sendov.l1_nil
attribute [local simp] Sendov.l1row_cons
attribute [local simp] Sendov.l1row_nil
attribute [local simp] Sendov.npev_cons
attribute [local simp] Sendov.npev_nil
attribute [local simp] Sendov.pevZ_cons
attribute [local simp] Sendov.pevZ_nil
attribute [local simp] Sendov.pev_cons
attribute [local simp] Sendov.pev_nil
attribute [local simp] Sendov.qrow_length
attribute [local simp] Sendov.rev_cons
attribute [local simp] Sendov.rev_nil
attribute [local simp] Sendov.rowZ_cons
attribute [local simp] Sendov.rowZ_length
attribute [local simp] Sendov.rowZ_nil
attribute [local simp] Sendov.rscale_length
attribute [local simp] Sendov.sumEraseProdC_zero
attribute [local simp] Sendov.sumEraseProd_zero
attribute [local simp] Sendov.unpackN_succ
attribute [local simp] Sendov.unpackN_zero
attribute [local simp] Sendov.unpackZ_succ
attribute [local simp] Sendov.unpackZ_zero
attribute [local simp] Sendov.wsumZ_cons
attribute [local simp] Sendov.wsumZ_nil
attribute [local simp] Sendov.wsum_cons
attribute [local simp] Sendov.wsum_nil



set_option autoImplicit false
open Sendov
open Polynomial
open Complex (I)
namespace Sendov
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hpa : p.eval (a : ℂ) = 0) :
    ∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - (a : ℂ)‖ < 1 := by
  by_contra hcon
  have hcrit : ∀ w : ℂ, (derivative p).eval w = 0 → 1 ≤ ‖w - (a : ℂ)‖ := by
    intro w hw
    by_contra hlt
    exact hcon ⟨w, hw, not_le.1 hlt⟩
  -- the two factorizations
  obtain ⟨z, hzcard, hz1, hpz⟩ := exists_root_multiset (by omega : 1 ≤ n) hdeg hroots hpa
  obtain ⟨q, hqcard, hq1, hq0, hpq⟩ := exists_crit_multiset hn hdeg hcrit
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have hc0 : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hp0
  have hpq' : derivative p = C ((n : ℂ) * p.leadingCoeff)
      * ((q.map (fun v => (a : ℂ) - v⁻¹)).map (fun w => X - C w)).prod := by
    simp only [Multiset.map_map, Function.comp_def]
    exact hpq
  -- basic numerology
  have hne : ((n : ℂ) - 1) ≠ 0 := by
    intro h
    have h1 : (n : ℂ) = 1 := by linear_combination h
    have h2 : n = 1 := by exact_mod_cast h1
    omega
  have hqne : q ≠ 0 := by
    intro h
    rw [h, Multiset.card_zero] at hqcard
    omega
  have haC0 : ((a : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt ha0
  have haC2 : ((a : ℝ) : ℂ) ^ 2 ≠ 1 := by
    intro h
    have : (a : ℂ) ^ 2 = ((a ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this] at h
    have h1 : a ^ 2 = 1 := by exact_mod_cast h
    nlinarith [h1, ha0, ha1]
  have hstar := one_le_integral_prod_norm hn (a := a)
    (by rw [abs_of_nonneg (le_of_lt ha0)]; linarith) hz1
    (polar_identity (c := p.leadingCoeff) (a := ((a : ℝ) : ℂ)) (n := n) (z := z) (q := q) (p := p)
      hc0 haC0 haC2 hzcard hqcard hq0 hpa hpz hpq')
    (prod_sub_mul_prod (c := p.leadingCoeff) (a := ((a : ℝ) : ℂ)) (n := n) (z := z) (q := q)
      (p := p) hc0 hq0 hpz hpq')
  -- the branch: low degree needs nothing further
  rcases (by omega : n < 5 ∨ 5 ≤ n) with hn5 | hn5
  · exact low_degree_contradiction hn (by omega) ha0 ha1 hqcard hq1 hstar
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn5
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  -- `x + iy` is the centroid of the `qⱼ`
  obtain ⟨x, y, hxy⟩ : ∃ x y : ℝ, q.sum = ((n : ℂ) - 1) * ((x : ℂ) + (y : ℂ) * I) := by
    refine ⟨(q.sum / ((n : ℂ) - 1)).re, (q.sum / ((n : ℂ) - 1)).im, ?_⟩
    rw [Complex.re_add_im, mul_div_cancel₀ _ hne]
  obtain ⟨hxre, hx2⟩ := xy_bounds hn hqcard hq1 hxy
  have hpolar := one_le_integral_Ppolar hn (a := a) (x := x) hqcard hq1 hxre hstar
  -- the origin channel
  have hcent := centroid_identity (c := p.leadingCoeff) (a := ((a : ℝ) : ℂ)) (n := n)
    (z := z) (q := q) (p := p) hn hc0 hzcard hqcard hpz hpq'
  have hfirst := first_origin_identity (c := p.leadingCoeff) (a := ((a : ℝ) : ℂ)) (n := n)
    (z := z) (q := q) (p := p) hc0 haC0 hzcard hq0 hpa hpz hpq'
  have hsecond := second_origin_identity (c := p.leadingCoeff) (a := ((a : ℝ) : ℂ)) (n := n)
    (z := z) (q := q) (p := p) hc0 hzcard hq0 hpz hpq'
  have horigin := origin_exact (n := n) (α := M n * (1 - a ^ 2) / 2) hn5 ha0 ha1 hqcard hqne
    hz1 hq1 hxy hcent hfirst hsecond rfl
  -- the two are incompatible
  exact polar_origin_incompatible hn5 ha0 ha1 (by nlinarith [hx2, sq_nonneg y]) rfl hpolar
    horigin
end Sendov
