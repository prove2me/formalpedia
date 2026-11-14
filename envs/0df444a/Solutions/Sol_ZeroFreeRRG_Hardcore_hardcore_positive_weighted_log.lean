-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.hardcore_positive_weighted_log
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:59:13.788752+00:00
-- url     : https://prove2.me/submissions/b408902b-cc82-4637-9a58-d7fa30dc9ee9

import Theorems.Thm_ZeroFreeRRG_Hardcore_nontrivial_size_bias_strict_coupling
import Theorems.Thm_ZeroFreeRRG_Hardcore_bounded_hardcore_expected_gap
import Theorems.Thm_ZeroFreeRRG_Hardcore_size_bias_gap_weighted_identity
import Mathlib
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (d : ℕ) (hd : 2 ≤ d) (θ C : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hbound : ∀ᵐ x ∂μ, 0 ≤ x ∧ x ≤ C)
    (hint : Integrable (fun x : ℝ => x) μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 1) (hne : μ ≠ Measure.dirac 1) :
    0 < ∫ xs : Fin d → ℝ, ((∏ i, xs i) - ∑ i, xs i + d - 1) *
      Real.log (1+θ*∏ i, xs i) ∂(Measure.pi fun _ : Fin d => μ) := by
  have hpos : ∀ᵐ x ∂μ, 0 ≤ x := hbound.mono (fun _ hx => hx.1)
  obtain ⟨π,hprob,hfst,hsnd,horder,hs,hprod⟩ :=
    nontrivial_size_bias_strict_coupling μ hpos hint hmean hne
  letI : IsProbabilityMeasure π := hprob
  have hf : ∀ᵐ p ∂π, 0 ≤ p.1 := by
    apply (ae_map_iff measurable_fst.aemeasurable (measurableSet_le measurable_const measurable_id)).1
    simpa [hfst] using hpos
  have hsize : ∀ᵐ x ∂(μ.withDensity (fun x => ENNReal.ofReal x)), x ≤ C :=
    (withDensity_absolutelyContinuous μ _).ae_le (hbound.mono (fun _ hx => hx.2))
  have hsbound : ∀ᵐ p ∂π, p.2 ≤ C := by
    apply (ae_map_iff measurable_snd.aemeasurable (measurableSet_le measurable_id measurable_const)).1
    simpa [hsnd] using hsize
  have hπbound : ∀ᵐ p ∂π, 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ C := by
    filter_upwards [hf,horder,hsbound] with p ha hb hc
    exact ⟨ha,hb,hc⟩
  have hp : 0 < π {p | 0 < p.1} := by
    have hz : 0 < μ {x | 0 < x} := by
      by_contra hn
      have hz : μ {x | 0 < x} = 0 := le_antisymm (not_lt.mp hn) bot_le
      have hno : ∀ᵐ x ∂μ, ¬0 < x := ae_iff.mpr (by simpa only [not_not] using hz)
      have heq : ∀ᵐ x ∂μ, x = 0 := by
        filter_upwards [hpos,hno] with x hx hn'
        exact le_antisymm (le_of_not_gt hn') hx
      have hh : (∫ x, x ∂μ) = 0 := by
        calc
          _ = ∫ _x, (0:ℝ) ∂μ := integral_congr_ae heq
          _ = 0 := integral_zero _ _
      linarith
    change 0 < μ (Ioi (0:ℝ)) at hz
    rw [← hfst, Measure.map_apply measurable_fst measurableSet_Ioi] at hz
    exact hz
  let ν := Measure.pi fun _ : Fin d => π
  let K := fun xs : Fin d → ℝ => Real.log (1+θ*∏ i, xs i)
  let g := fun (xs : Fin d → ℝ × ℝ) (S : Finset (Fin d)) =>
    K (fun i => if i ∈ S then (xs i).2 else (xs i).1)
  have hK : Measurable K := by dsimp [K]; fun_prop
  have hgood : ∀ᵐ xs ∂ν, ∀ a, 0 ≤ (xs a).1 ∧ (xs a).1 ≤ (xs a).2 ∧ (xs a).2 ≤ C := by
    apply Measure.ae_pi_le_pi
    exact Filter.eventually_pi (fun _ : Fin d => hπbound)
  have hlogcont : ContinuousOn Real.log (Icc (1:ℝ) (1+θ*C^d)) := by
    apply Real.continuousOn_log.mono
    intro x hx
    simp only [mem_Icc,mem_compl_iff,mem_singleton_iff] at *
    linarith [hx.1]
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc (1:ℝ) (1+θ*C^d))).exists_bound_of_continuousOn hlogcont
  have hgi (S : Finset (Fin d)) : Integrable (fun xs => g xs S) ν := by
    have hm : Measurable (fun xs : Fin d → ℝ × ℝ => g xs S) := by
      dsimp [g,K]
      have hprod : Measurable (fun xs : Fin d → ℝ × ℝ =>
          ∏ a, if a ∈ S then (xs a).2 else (xs a).1) := by
        apply Finset.measurable_prod
        intro a ha
        by_cases h : a ∈ S
        · simp only [h,if_true]; exact measurable_snd.comp (measurable_pi_apply a)
        · simp only [h,if_false]; exact measurable_fst.comp (measurable_pi_apply a)
      exact (measurable_const.add (measurable_const.mul hprod)).log
    apply Integrable.of_bound hm.aestronglyMeasurable B
    filter_upwards [hgood] with xs hx
    have hp0 (a : Fin d) : 0 ≤ (if a ∈ S then (xs a).2 else (xs a).1) := by
      split_ifs <;> linarith [(hx a).1,(hx a).2.1]
    have hpC (a : Fin d) : (if a ∈ S then (xs a).2 else (xs a).1) ≤ C := by
      split_ifs <;> linarith [(hx a).2.1,(hx a).2.2]
    have hprod0 : 0 ≤ ∏ a : Fin d, (if a ∈ S then (xs a).2 else (xs a).1) :=
      Finset.prod_nonneg (fun a _ => hp0 a)
    have hprodC : (∏ a : Fin d, (if a ∈ S then (xs a).2 else (xs a).1)) ≤ C^d := by
      calc
        _ ≤ ∏ _a : Fin d, C := Finset.prod_le_prod (fun a _ => hp0 a) (fun a _ => hpC a)
        _ = _ := by simp
    have harg : 1+θ*∏ a : Fin d, (if a ∈ S then (xs a).2 else (xs a).1) ∈ Icc (1:ℝ) (1+θ*C^d) := by
      constructor
      · nlinarith [mul_nonneg hθ.le hprod0]
      · nlinarith [mul_nonneg hθ.le (sub_nonneg.mpr hprodC)]
    exact hB _ harg
  have hgap := bounded_hardcore_expected_gap d hd θ C hθ hC π hπbound hs hp
  have hid := size_bias_gap_weighted_identity d μ hint hpos π hfst hsnd K hK hgi
  have hmax : ∀ᵐ xs ∂(Measure.pi fun _ : Fin d => μ), ∀ i, 0 ≤ xs i := by
    apply Measure.ae_pi_le_pi
    exact Filter.eventually_pi (fun _ : Fin d => hpos)
  have hpoly (xs : Fin d → ℝ) :
      (∏ i, if i ∈ Finset.univ then max (xs i) 0 else 1) * K xs -
        (∏ i, if i ∈ (∅ : Finset (Fin d)) then max (xs i) 0 else 1) * K xs -
        ∑ j, ((∏ i, if i ∈ ({j} : Finset (Fin d)) then max (xs i) 0 else 1) * K xs -
          (∏ i, if i ∈ (∅ : Finset (Fin d)) then max (xs i) 0 else 1) * K xs) =
      ((∏ i, max (xs i) 0) - ∑ i, max (xs i) 0 + d - 1) * K xs := by
    simp only [Finset.mem_univ, if_true, Finset.notMem_empty, if_false, Finset.prod_const_one,
      one_mul, Finset.mem_singleton, Finset.prod_ite_eq', Finset.sum_sub_distrib,
      ← Finset.sum_mul]
    simp
    ring
  have hidentity : (∫ xs : Fin d → ℝ × ℝ, g xs Finset.univ - g xs ∅ - ∑ i, (g xs {i}-g xs ∅) ∂ν) =
      ∫ xs : Fin d → ℝ, ((∏ i, xs i) - ∑ i, xs i + d - 1) * K xs ∂(Measure.pi fun _ : Fin d => μ) := by
    rw [hid]
    apply integral_congr_ae
    filter_upwards [hmax] with xs hx
    rw [hpoly]
    simp only [max_eq_left (hx _)]
  change 0 < (∫ xs : Fin d → ℝ × ℝ, g xs Finset.univ - g xs ∅ - ∑ i, (g xs {i}-g xs ∅) ∂ν) at hgap
  rw [hidentity] at hgap
  exact hgap
