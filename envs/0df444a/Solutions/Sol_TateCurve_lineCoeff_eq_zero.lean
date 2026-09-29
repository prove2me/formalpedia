-- Prove2me | solution 1 for TateCurve.lineCoeff_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/fe0b38e0-d2cc-57e1-b99f-2f87a30fa375

import Mathlib
import Mathlib.NumberTheory.Padics.PadicNumbers
import Definitions.Def_TateCurve_QShift
import Theorems.Thm_TateCurve_defect_qExpansion
import Theorems.Thm_TateCurve_pointX_q_mul
import Theorems.Thm_TateCurve_pointY_q_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TateCurve_lineCoeff_eq_zero

open scoped NNReal
open IsUltrametricDist Filter Finset
p2m_open "TateCurve P2MW.S_TateCurve_lineCoeff_eq_zero.TateCurve"

namespace TateCurve
p2m_export "TateCurve" "ne_zero_of_one_lt_norm ne_one_of_one_lt_norm norm_q_lt_one_of_qshift qshift_lattice_ne_one qshift_lattice_ne_one_shifted qshift_annulus_at_u qshift_annulus_at_shifted qshiftAlpha qshiftBeta qshiftGamma norm_inv_lt_one_of_one_lt_norm norm_qshiftBeta_le_one norm_qshiftAlpha_le norm_qshiftGamma_le lineCoeff_eq_zero_of_qshift coeff_eq_of_forall_tsum_eq hubTerm alphaTerm betaTerm gammaTerm hubTerm_eq summable_alphaTerm summable_betaTerm summable_gammaTerm tsum_alphaTerm tsum_betaTerm tsum_gammaTerm tsum_hubTerm summable_defect_series summable_qshift_series lineCoeff defectCoeff pointX pointY a₄ a₆ defect_qExpansion pointX_q_mul pointY_q_mul"
p2m_open "TateCurve"

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

private theorem four_mul_defectCoeff_eq_qshift' [CharZero K] {u : K} (hu : 1 < ‖u‖) (M : ℕ) :
    (4 : K) * defectCoeff u M = qshiftAlpha u M + qshiftBeta u M + qshiftGamma M := by
  have hu0 : u ≠ 0 := ne_zero_of_one_lt_norm hu
  have hu1 : u ≠ 1 := ne_one_of_one_lt_norm hu
  have hu_norm_pos : (0 : ℝ) < ‖u‖ := lt_trans one_pos hu

  have hq₀0 : u⁻¹ * u⁻¹ ≠ 0 := mul_ne_zero (inv_ne_zero hu0) (inv_ne_zero hu0)
  have huinv_lt : ‖u⁻¹‖ < 1 := norm_inv_lt_one_of_one_lt_norm hu
  have huinv_pos : (0 : ℝ) < ‖u⁻¹‖ := norm_pos_iff.mpr (inv_ne_zero hu0)
  have hq₀norm : ‖u⁻¹ * u⁻¹‖ = ‖u⁻¹‖ * ‖u⁻¹‖ := norm_mul _ _
  have hq₀1 : ‖u⁻¹ * u⁻¹‖ < 1 := by
    rw [hq₀norm]
    nlinarith

  have hregion : ∀ q : K, q ≠ 0 → ‖q‖ ≤ ‖u⁻¹ * u⁻¹‖ → ‖q‖ * ‖u‖ < 1 := by
    intro q hq hqle
    have h1 : ‖u⁻¹‖ * ‖u‖ = 1 := by
      rw [norm_inv]
      field_simp
    have h2 : ‖q‖ ≤ ‖u⁻¹‖ * ‖u⁻¹‖ := by rwa [hq₀norm] at hqle
    nlinarith

  have ha : ∀ q : K, q ≠ 0 → ‖q‖ ≤ ‖u⁻¹ * u⁻¹‖ →
      Summable fun N => (4 * defectCoeff u N) * q ^ N := fun q hq hqle =>
    summable_defect_series hu (hregion q hq hqle)
  have hb : ∀ q : K, q ≠ 0 → ‖q‖ ≤ ‖u⁻¹ * u⁻¹‖ →
      Summable fun N => (qshiftAlpha u N + qshiftBeta u N + qshiftGamma N) * q ^ N :=
    fun q hq hqle => summable_qshift_series hu (hregion q hq hqle)
  have heq : ∀ q : K, q ≠ 0 → ‖q‖ ≤ ‖u⁻¹ * u⁻¹‖ →
      ∑' N, (4 * defectCoeff u N) * q ^ N
        = ∑' N, (qshiftAlpha u N + qshiftBeta u N + qshiftGamma N) * q ^ N := by
    intro q hq hqle
    have hqu : ‖q‖ * ‖u‖ < 1 := hregion q hq hqle
    have hq1 : ‖q‖ < 1 := norm_q_lt_one_of_qshift hu hqu
    have hq1' : ‖q‖₊ < 1 := by exact_mod_cast hq1
    have hlat : ∀ n : ℤ, q ^ n * u ≠ 1 := qshift_lattice_ne_one hq hu hqu
    have hlat' : ∀ n : ℤ, q ^ n * (q * u) ≠ 1 := qshift_lattice_ne_one_shifted hq hu hqu
    have hann := qshift_annulus_at_u (q := q) hu hqu
    have hann' := qshift_annulus_at_shifted hq hu hqu
    have hqu0 : q * u ≠ 0 := mul_ne_zero hq hu0
    have hexp_u := defect_qExpansion hq hq1' hu0 hlat hann.1 hann.2
    have hexp_qu := defect_qExpansion hq hq1' hqu0 hlat' hann'.1 hann'.2

    have hshift : pointY q u ^ 2 + pointX q u * pointY q u
        - (pointX q u ^ 3 + a₄ q * pointX q u + a₆ q)
        = pointY q (q * u) ^ 2 + pointX q (q * u) * pointY q (q * u)
        - (pointX q (q * u) ^ 3 + a₄ q * pointX q (q * u) + a₆ q) := by
      rw [pointX_q_mul hq, pointY_q_mul hq]

    have hSα : Summable fun M => qshiftAlpha u M * q ^ M := by
      have hr0 : (0 : ℝ) ≤ ‖q‖ * ‖u‖ := mul_nonneg (norm_nonneg q) (norm_nonneg u)
      have hcompare : Summable fun M : ℕ => ((M : ℝ) + 1) * (‖q‖ * ‖u‖) ^ M := by
        have h1 : Summable fun M : ℕ => (M : ℝ) * (‖q‖ * ‖u‖) ^ M := by
          have h2 := summable_pow_mul_geometric_of_norm_lt_one (r := (‖q‖ * ‖u‖ : ℝ)) 1
            (by rwa [Real.norm_of_nonneg hr0])
          exact h2.congr fun M => by rw [pow_one]
        have h3 : Summable fun M : ℕ => (‖q‖ * ‖u‖) ^ M := summable_geometric_of_lt_one hr0 hqu
        exact (h1.add h3).congr fun M => by ring
      refine Summable.of_norm (Summable.of_nonneg_of_le (fun M => norm_nonneg _)
        (fun M => ?_) hcompare)
      have hα := norm_qshiftAlpha_le (u := u) hu M
      rw [norm_mul, norm_pow]
      have h2 : ‖u‖ ^ M * ‖q‖ ^ M = (‖q‖ * ‖u‖) ^ M := by rw [← mul_pow]; ring_nf
      have h3 : (0 : ℝ) ≤ ‖q‖ ^ M := pow_nonneg (norm_nonneg q) _
      nlinarith [norm_nonneg (qshiftAlpha u M), pow_nonneg (norm_nonneg u) M]
    have hSβ : Summable fun M => qshiftBeta u M * q ^ M := by
      refine Summable.of_norm (Summable.of_nonneg_of_le (fun M => norm_nonneg _) (fun M => ?_)
        (summable_geometric_of_lt_one (norm_nonneg q) hq1))
      have hβ := norm_qshiftBeta_le_one (u := u) hu M
      rw [norm_mul, norm_pow]
      have h3 : (0 : ℝ) ≤ ‖q‖ ^ M := pow_nonneg (norm_nonneg q) _
      nlinarith [norm_nonneg (qshiftBeta u M)]
    have hSγ : Summable fun M => (qshiftGamma M : K) * q ^ M := by
      have hcompare : Summable fun M : ℕ => 2 * ((M : ℝ) + 1) * ‖q‖ ^ M := by
        have h1 : Summable fun M : ℕ => (M : ℝ) * ‖q‖ ^ M := by
          have h2 := summable_pow_mul_geometric_of_norm_lt_one (r := (‖q‖ : ℝ)) 1
            (by rwa [Real.norm_of_nonneg (norm_nonneg q)])
          exact h2.congr fun M => by rw [pow_one]
        exact ((h1.add (summable_geometric_of_lt_one (norm_nonneg q) hq1)).mul_left 2).congr
          fun M => by ring
      refine Summable.of_norm (Summable.of_nonneg_of_le (fun M => norm_nonneg _)
        (fun M => ?_) hcompare)
      have hγ := norm_qshiftGamma_le (K := K) M
      rw [norm_mul, norm_pow]
      have h3 : (0 : ℝ) ≤ ‖q‖ ^ M := pow_nonneg (norm_nonneg q) _
      nlinarith [norm_nonneg (qshiftGamma M : K)]

    calc ∑' N, (4 * defectCoeff u N) * q ^ N
        = 4 * ∑' N, defectCoeff u N * q ^ N := by
          rw [← tsum_mul_left]
          exact tsum_congr fun N => by ring
      _ = 4 * ∑' N, defectCoeff (q * u) N * q ^ N := by rw [← hexp_u, ← hexp_qu, hshift]
      _ = ∑' N, (4 * defectCoeff (q * u) N) * q ^ N := by
          rw [← tsum_mul_left]
          exact tsum_congr fun N => by ring
      _ = ∑' p : ℕ × ℕ, hubTerm u q p := (tsum_hubTerm hu hq hqu).symm
      _ = ∑' p : ℕ × ℕ, (alphaTerm u q p + betaTerm u q p + gammaTerm q p) :=
          tsum_congr fun p => hubTerm_eq hq hu0 p
      _ = (∑' p : ℕ × ℕ, (alphaTerm u q p + betaTerm u q p)) + ∑' p : ℕ × ℕ, gammaTerm q p :=
          ((summable_alphaTerm hu hqu).add (summable_betaTerm hu hqu)).tsum_add
            (summable_gammaTerm hu hqu)
      _ = ((∑' p : ℕ × ℕ, alphaTerm u q p) + ∑' p : ℕ × ℕ, betaTerm u q p)
            + ∑' p : ℕ × ℕ, gammaTerm q p := by
          rw [(summable_alphaTerm hu hqu).tsum_add (summable_betaTerm hu hqu)]
      _ = ((∑' M, qshiftAlpha u M * q ^ M) + ∑' M, qshiftBeta u M * q ^ M)
            + ∑' M, (qshiftGamma M : K) * q ^ M := by
          rw [tsum_alphaTerm hu hqu, tsum_betaTerm hu hqu, tsum_gammaTerm hu hqu]
      _ = (∑' M, (qshiftAlpha u M * q ^ M + qshiftBeta u M * q ^ M))
            + ∑' M, (qshiftGamma M : K) * q ^ M := by
          rw [hSα.tsum_add hSβ]
      _ = ∑' M, ((qshiftAlpha u M * q ^ M + qshiftBeta u M * q ^ M)
            + (qshiftGamma M : K) * q ^ M) := by
          rw [(hSα.add hSβ).tsum_add hSγ]
      _ = ∑' N, (qshiftAlpha u N + qshiftBeta u N + qshiftGamma N) * q ^ N :=
          tsum_congr fun N => by ring
  exact coeff_eq_of_forall_tsum_eq hq₀0 hq₀1 ha hb heq M

end TateCurve

theorem solution : ∀ N k : ℕ, 1 ≤ k → k ≤ N → lineCoeff N k = 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact lineCoeff_eq_zero_of_qshift (K := ℚ_[2])
    fun v hv M => TateCurve.four_mul_defectCoeff_eq_qshift' hv M

end S_TateCurve_lineCoeff_eq_zero
end P2MW
export P2MW.S_TateCurve_lineCoeff_eq_zero (solution)
