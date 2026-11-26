-- Prove2me | solution 1 for PVM.ofReal_norm_sq_integral_sub_unboundedIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:01:11.116779+00:00
-- url     : https://prove2.me/submissions/7b3bb489-f897-45ae-8fcf-7b3b7ba88e0f

import Definitions.Def_Spectral_PVM_Integral
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Function.L2Space
import Definitions.Def_Spectral_PVM_Unbounded
import Theorems.Thm_PVM_integral_sub
import Theorems.Thm_PVM_simpleIntegral_one
import Theorems.Thm_PVM_simpleIntegral_zero
attribute [local simp] PVM.simpleIntegral_one
attribute [local simp] PVM.simpleIntegral_zero


section
open MeasureTheory
open Function
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
private theorem PVM.spectralTruncation_tendsto (f : ℝ → ℂ) (t : ℝ) :
    Filter.Tendsto (fun n => PVM.spectralTruncation f n t)
      Filter.atTop (nhds (f t)) := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖f t‖
  refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_
  rw [PVM.spectralTruncation, if_pos]
  exact hN.trans (Nat.cast_le.2 hn)
open Filter
end

set_option autoImplicit false
open MeasureTheory
open Function
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PVM
theorem _root_.solution (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) (hbdd : ∃ C, ∀ r, ‖f r‖ ≤ C)
    (g : ℝ → ℂ) (hg : Measurable g)
    (x : (E_pvm.unboundedIntegral g hg).domain) :
    ENNReal.ofReal
        (‖E_pvm.integral f hf hbdd (x : E) - E_pvm.unboundedIntegral g hg x‖ ^ 2) =
      ∫⁻ r, ‖f r - g r‖₊ ^ 2 ∂(E_pvm.scalarMeasure (x : E)) := by
  let C : ℝ := Classical.choose hbdd
  have hC : ∀ r, ‖f r‖ ≤ C := Classical.choose_spec hbdd
  have hC_nonneg : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
  let gn : ℕ → ℝ → ℂ := fun n => PVM.spectralTruncation g n
  have hgn_meas (n : ℕ) : Measurable (gn n) :=
    PVM.spectralTruncation_measurable g hg n
  have hgn_bdd (n : ℕ) : ∀ r, ‖gn n r‖ ≤ n :=
    PVM.norm_spectralTruncation_le g n
  have hgn_norm (n : ℕ) (r : ℝ) : ‖gn n r‖ ≤ ‖g r‖ := by
    unfold gn PVM.spectralTruncation
    by_cases hr : ‖g r‖ ≤ n
    · rw [if_pos hr]
    · rw [if_neg hr, norm_zero]
      exact norm_nonneg _
  have hdiff_bdd (n : ℕ) : ∀ r, ‖(f - gn n) r‖ ≤ C + n := by
    intro r
    change ‖f r - gn n r‖ ≤ C + n
    exact (norm_sub_le _ _).trans (add_le_add (hC r) (hgn_bdd n r))
  have hidentity (n : ℕ) :
      ENNReal.ofReal
          (‖E_pvm.integral f hf hbdd (x : E) -
            E_pvm.truncatedIntegral g hg n (x : E)‖ ^ 2) =
        ∫⁻ r, ‖f r - gn n r‖₊ ^ 2 ∂(E_pvm.scalarMeasure (x : E)) := by
    have hL2 := E_pvm.ofReal_norm_sq_integral
      (f - gn n) (hf.sub (hgn_meas n)) ⟨C + n, hdiff_bdd n⟩ (x : E)
    rw [E_pvm.integral_sub f (gn n) hf (hgn_meas n) hbdd
      ⟨n, hgn_bdd n⟩ ⟨C + n, hdiff_bdd n⟩] at hL2
    simpa only [PVM.truncatedIntegral, gn, Pi.sub_apply, sub_apply] using hL2
  have htrunc := (E_pvm.cauchySeq_truncatedIntegral g hg x).tendsto_limUnder
  change Filter.Tendsto
    (fun n => E_pvm.truncatedIntegral g hg n (x : E)) Filter.atTop
    (nhds (E_pvm.unboundedIntegral g hg x)) at htrunc
  have hleft : Filter.Tendsto
      (fun n => ENNReal.ofReal
        (‖E_pvm.integral f hf hbdd (x : E) -
          E_pvm.truncatedIntegral g hg n (x : E)‖ ^ 2))
      Filter.atTop
      (nhds (ENNReal.ofReal
        (‖E_pvm.integral f hf hbdd (x : E) - E_pvm.unboundedIntegral g hg x‖ ^ 2))) := by
    exact ENNReal.tendsto_ofReal ((tendsto_const_nhds.sub htrunc).norm.pow 2)
  have hgSq_meas : Measurable
      (fun r => (↑(‖g r‖₊ ^ 2) : ENNReal)) :=
    ((hg.nnnorm.pow_const 2).coe_nnreal_ennreal)
  let bound : ℝ → ENNReal := fun r =>
    2 * (ENNReal.ofReal (C ^ 2) + (↑(‖g r‖₊ ^ 2) : ENNReal))
  have hbound_meas : Measurable bound := by
    unfold bound
    exact measurable_const.mul (measurable_const.add hgSq_meas)
  have hpoint_bound (n : ℕ) (r : ℝ) :
      (↑(‖f r - gn n r‖₊ ^ 2) : ENNReal) ≤ bound r := by
    have hnorm : ‖f r - gn n r‖ ≤ C + ‖g r‖ :=
      (norm_sub_le _ _).trans (add_le_add (hC r) (hgn_norm n r))
    have hsquare : ‖f r - gn n r‖ ^ 2 ≤ 2 * (C ^ 2 + ‖g r‖ ^ 2) := by
      calc
        ‖f r - gn n r‖ ^ 2 ≤ (C + ‖g r‖) ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _) (add_nonneg hC_nonneg (norm_nonneg _))).2 hnorm
        _ ≤ 2 * (C ^ 2 + ‖g r‖ ^ 2) := add_sq_le
    change ‖f r - gn n r‖ₑ ^ 2 ≤ bound r
    calc
      ‖f r - gn n r‖ₑ ^ 2 = ENNReal.ofReal (‖f r - gn n r‖ ^ 2) := by
        rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]
      _ ≤ ENNReal.ofReal (2 * (C ^ 2 + ‖g r‖ ^ 2)) :=
        ENNReal.ofReal_le_ofReal hsquare
      _ = bound r := by
        unfold bound
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ENNReal.ofReal_add (sq_nonneg C) (sq_nonneg ‖g r‖),
          ENNReal.ofReal_pow (norm_nonneg (g r)) 2, ofReal_norm,
          enorm_eq_nnnorm, ENNReal.coe_pow]
        norm_num
  have hbound_finite : (∫⁻ r, bound r ∂(E_pvm.scalarMeasure (x : E))) ≠ ⊤ := by
    have hconst :
        (∫⁻ _r : ℝ, ENNReal.ofReal (C ^ 2) ∂(E_pvm.scalarMeasure (x : E))) < ⊤ := by
      rw [lintegral_const]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (E_pvm.scalarMeasure_lt_top (x : E) Set.univ)
    have hsum :
        (∫⁻ r, ENNReal.ofReal (C ^ 2) + (↑(‖g r‖₊ ^ 2) : ENNReal)
          ∂(E_pvm.scalarMeasure (x : E))) < ⊤ := by
      rw [lintegral_add_left measurable_const]
      exact (ENNReal.add_lt_top).2 ⟨hconst, x.property⟩
    unfold bound
    have hmul :
        (∫⁻ r, (2 : ENNReal) *
          (ENNReal.ofReal (C ^ 2) + (↑(‖g r‖₊ ^ 2) : ENNReal))
            ∂(E_pvm.scalarMeasure (x : E))) =
          2 * ∫⁻ r, ENNReal.ofReal (C ^ 2) +
            (↑(‖g r‖₊ ^ 2) : ENNReal) ∂(E_pvm.scalarMeasure (x : E)) :=
      lintegral_const_mul 2 (measurable_const.add hgSq_meas)
    rw [hmul]
    exact (ENNReal.mul_lt_top (by norm_num) hsum).ne
  have hright : Filter.Tendsto
      (fun n => ∫⁻ r, (↑(‖f r - gn n r‖₊ ^ 2) : ENNReal)
        ∂(E_pvm.scalarMeasure (x : E)))
      Filter.atTop
      (nhds (∫⁻ r, (↑(‖f r - g r‖₊ ^ 2) : ENNReal)
        ∂(E_pvm.scalarMeasure (x : E)))) := by
    apply tendsto_lintegral_of_dominated_convergence bound
    · intro n
      exact ((hf.sub (hgn_meas n)).nnnorm.pow_const 2).coe_nnreal_ennreal
    · intro n
      exact ae_of_all _ (hpoint_bound n)
    · exact hbound_finite
    · apply ae_of_all
      intro r
      have hsub : Filter.Tendsto (fun n => f r - gn n r) Filter.atTop
          (nhds (f r - g r)) :=
        tendsto_const_nhds.sub (PVM.spectralTruncation_tendsto g r)
      have hreal := ENNReal.tendsto_ofReal (hsub.norm.pow 2)
      convert hreal using 1
      · ext n
        rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm,
          enorm_eq_nnnorm, ENNReal.coe_pow]
      · rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm,
          enorm_eq_nnnorm, ENNReal.coe_pow]
  apply tendsto_nhds_unique hleft
  convert hright using 1
  · ext n
    exact hidentity n
  · congr 1
end PVM
