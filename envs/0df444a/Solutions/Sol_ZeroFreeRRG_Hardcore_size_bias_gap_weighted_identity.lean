-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.size_bias_gap_weighted_identity
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:58:22.139203+00:00
-- url     : https://prove2.me/submissions/982bf0bf-f26a-4ac0-ba3a-a32c2fed824b

import Theorems.Thm_ZeroFreeRRG_Hardcore_size_bias_coupling_expectation
import Theorems.Thm_ZeroFreeRRG_Hardcore_size_bias_coupling_product_law
import Mathlib
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators ENNReal

theorem solution (d : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (fun x : ℝ => x) μ) (hpos : ∀ᵐ x ∂μ, 0 ≤ x)
    (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π]
    (hfst : Measure.map Prod.fst π = μ)
    (hsnd : Measure.map Prod.snd π = μ.withDensity (fun x => ENNReal.ofReal x))
    (K : (Fin d → ℝ) → ℝ) (hK : Measurable K)
    (hgi : ∀ S : Finset (Fin d), Integrable
      (fun xs : Fin d → ℝ × ℝ => K (fun i => if i ∈ S then (xs i).2 else (xs i).1))
      (Measure.pi fun _ : Fin d => π)) :
    let g := fun (xs : Fin d → ℝ × ℝ) (S : Finset (Fin d)) =>
      K (fun i => if i ∈ S then (xs i).2 else (xs i).1)
    let w := fun (xs : Fin d → ℝ) (S : Finset (Fin d)) =>
      (∏ i, if i ∈ S then max (xs i) 0 else 1) * K xs
    (∫ xs, g xs Finset.univ - g xs ∅ - ∑ i, (g xs {i}-g xs ∅)
      ∂(Measure.pi fun _ : Fin d => π)) =
    ∫ xs, w xs Finset.univ - w xs ∅ - ∑ i, (w xs {i}-w xs ∅)
      ∂(Measure.pi fun _ : Fin d => μ) := by
  dsimp only
  let ν := Measure.pi (fun _ : Fin d => π)
  let σ := Measure.pi (fun _ : Fin d => μ)
  let g := fun (xs : Fin d → ℝ × ℝ) (S : Finset (Fin d)) =>
    K (fun i => if i ∈ S then (xs i).2 else (xs i).1)
  let w := fun (xs : Fin d → ℝ) (S : Finset (Fin d)) =>
    (∏ i, if i ∈ S then max (xs i) 0 else 1) * K xs
  have hwi (S : Finset (Fin d)) : Integrable (fun xs => w xs S) σ := by
    let P := fun xs : Fin d → ℝ × ℝ => fun i => if i ∈ S then (xs i).2 else (xs i).1
    let ρ := fun xs : Fin d → ℝ => ∏ i, if i ∈ S then max (xs i) 0 else 1
    have hP : Measurable P := by
      apply measurable_pi_lambda
      intro i
      dsimp [P]
      split_ifs <;> fun_prop
    have hρ : Measurable ρ := by
      dsimp [ρ]
      apply Finset.measurable_prod
      intro i hi
      split_ifs <;> fun_prop
    have hρ0 (xs : Fin d → ℝ) : 0 ≤ ρ xs := by
      dsimp [ρ]
      exact Finset.prod_nonneg (fun i _ => by split_ifs <;> positivity)
    have hmap : Integrable K (Measure.map P ν) := by
      exact (integrable_map_measure hK.aestronglyMeasurable hP.aemeasurable).2 (hgi S)
    rw [size_bias_coupling_product_law d S μ hint hpos π hfst hsnd] at hmap
    have := (integrable_withDensity_iff_integrable_smul₀' hρ.ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).1 hmap
    apply this.congr
    exact Filter.Eventually.of_forall (fun xs => by simp only [ENNReal.toReal_ofReal (hρ0 xs),smul_eq_mul]; rfl)
  have heq (S : Finset (Fin d)) : (∫ xs, g xs S ∂ν) = ∫ xs, w xs S ∂σ :=
    size_bias_coupling_expectation d S μ hint hpos π hfst hsnd K hK
  have hg (S : Finset (Fin d)) : Integrable (fun xs => g xs S) ν := hgi S
  have hgs : Integrable (fun xs => ∑ i, (g xs {i}-g xs ∅)) ν := by
    apply integrable_finsetSum
    intro i hi
    exact (hg {i}).sub (hg ∅)
  have hws : Integrable (fun xs => ∑ i, (w xs {i}-w xs ∅)) σ := by
    apply integrable_finsetSum
    intro i hi
    exact (hwi {i}).sub (hwi ∅)
  change (∫ xs, g xs Finset.univ - g xs ∅ - ∑ i, (g xs {i}-g xs ∅) ∂ν) =
    ∫ xs, w xs Finset.univ - w xs ∅ - ∑ i, (w xs {i}-w xs ∅) ∂σ
  have hL := integral_sub ((hg Finset.univ).sub (hg ∅)) hgs
  have hR := integral_sub ((hwi Finset.univ).sub (hwi ∅)) hws
  simp only [Pi.sub_apply] at hL hR
  rw [hL, hR, integral_sub (hg Finset.univ) (hg ∅),
      integral_sub (hwi Finset.univ) (hwi ∅)]
  have hsg := integral_finsetSum (μ := ν) (f := fun i xs => g xs {i} - g xs ∅)
    Finset.univ (fun i hi => (hg {i}).sub (hg ∅))
  have hsw := integral_finsetSum (μ := σ) (f := fun i xs => w xs {i} - w xs ∅)
    Finset.univ (fun i hi => (hwi {i}).sub (hwi ∅))
  rw [hsg,hsw]
  simp_rw [integral_sub (hg _) (hg ∅), integral_sub (hwi _) (hwi ∅), heq]
