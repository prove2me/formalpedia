-- Prove2me | solution 1 for ProcessingNetworks.Stability.arrival_process_slln
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:53:11.959204+00:00
-- url     : https://prove2.me/submissions/c1b514ef-284c-4669-85b0-5c111fd0d76f

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_BaselineAssumptions

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace ProcessingNetworks.Stability.APS

/-- The mean of the Poisson distribution. -/
theorem aps_poisson_hasSum (r : ℝ≥0) :
    HasSum (fun n : ℕ => (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ)) • (n : ℝ)) (r : ℝ) := by
  have he : HasSum (fun n : ℕ => (r : ℝ) ^ n / (n.factorial : ℝ)) (Real.exp r) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (r : ℝ)
  have h1 : HasSum (fun m : ℕ => (Real.exp (-(r : ℝ)) * (r : ℝ)) * ((r : ℝ) ^ m / (m.factorial : ℝ)))
      ((Real.exp (-(r : ℝ)) * (r : ℝ)) * Real.exp r) := he.mul_left _
  have hval : (Real.exp (-(r : ℝ)) * (r : ℝ)) * Real.exp r = (r : ℝ) := by
    rw [mul_comm (Real.exp _) _, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  rw [hval] at h1
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.sum_range_one, Nat.cast_zero, smul_zero, sub_zero]
  have hfe : (fun m : ℕ => Real.exp (-(r : ℝ)) * (r : ℝ) * ((r : ℝ) ^ m / (m.factorial : ℝ))) =
      fun n : ℕ => (Real.exp (-(r : ℝ)) * (r : ℝ) ^ (n + 1) / ((n + 1).factorial : ℝ)) •
        ((n + 1 : ℕ) : ℝ) := by
    funext m
    rw [Nat.factorial_succ, smul_eq_mul]
    push_cast
    field_simp
    ring
  rw [hfe] at h1
  exact h1

end ProcessingNetworks.Stability.APS

open ProcessingNetworks.Stability ProcessingNetworks.Stability.APS in
theorem solution {Ω : Type*} [MeasureSpace Ω] {I J : ℕ} {N0 : Fin J → ℕ}
    {E : Fin I → ℝ → Ω → ℕ} {lam : Fin I → ℝ≥0}
    {v : Fin J → ℕ → Ω → ℝ} {φ : Fin J → ℕ → Ω → Fin I → ℕ}
    {m : Fin J → ℝ} {Γ : Fin J → Fin I → ℝ} {Psi : Fin J → ℕ → Ω → ℝ × (Fin I → ℕ)}
    (h : BaselineAssumptions I J N0 E lam v φ m Γ Psi) (i : Fin I) :
    ℙ {ω | Tendsto (fun t : ℝ => (E i t ω : ℝ) / t) atTop (nhds (lam i : ℝ))} = 1 := by
  obtain ⟨hE0, hEmono, hinc⟩ := h.poisson i
  set r := lam i with hr
  set Y : ℕ → Ω → ℕ := fun k ω => E i ((k : ℝ) + 1) ω - E i (k : ℝ) ω with hY
  set X : ℕ → Ω → ℝ := fun k ω => (Y k ω : ℝ) with hX
  have key : ∀ n : ℕ, iIndepFun (fun k : Fin n => Y k) ℙ ∧
      ∀ k : Fin n, Measure.map (Y k) ℙ = poissonMeasure r := by
    intro n
    obtain ⟨h1, h2⟩ := hinc n (fun k => ((k : ℕ) : ℝ))
      (fun a b hab => by simp only; exact_mod_cast hab) (by simp)
    have e : ∀ k : Fin n, (fun ω => E i (((k.succ : Fin (n + 1)) : ℕ) : ℝ) ω -
        E i (((k.castSucc : Fin (n + 1)) : ℕ) : ℝ) ω) = Y k := by
      intro k; funext ω; simp [hY, Fin.val_succ]
    refine ⟨?_, fun k => ?_⟩
    · convert h1 using 1
      funext k
      exact (e k).symm
    · rw [← e k, h2 k]
      congr 1
      simp [Fin.val_succ]
  have hmap : ∀ k, Measure.map (Y k) ℙ = poissonMeasure r := fun k => (key (k + 1)).2 ⟨k, by omega⟩
  have haem : ∀ k, AEMeasurable (Y k) ℙ := fun k =>
    AEMeasurable.of_map_ne_zero (by rw [hmap k]; exact IsProbabilityMeasure.ne_zero _)
  have hident : ∀ k, IdentDistrib (X k) (X 0) ℙ ℙ := by
    intro k
    have hY : IdentDistrib (Y k) (Y 0) ℙ ℙ := ⟨haem k, haem 0, by rw [hmap k, hmap 0]⟩
    exact hY.comp (u := fun n : ℕ => (n : ℝ)) measurable_from_nat
  have hindep : Pairwise (Function.onFun (· ⟂ᵢ[ℙ] ·) X) := by
    intro a b hab
    have hI := (key (max a b + 1)).1
    have h2 := hI.indepFun (i := ⟨a, by omega⟩) (j := ⟨b, by omega⟩)
      (fun h => hab (by simpa using congrArg Fin.val h))
    exact h2.comp (φ := fun n : ℕ => (n : ℝ)) (ψ := fun n : ℕ => (n : ℝ))
      measurable_from_nat measurable_from_nat
  have hpo := aps_poisson_hasSum r
  have hintpo : Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure r) := by
    rw [integrable_poissonMeasure_iff]
    have := hpo.summable
    refine this.congr fun n => ?_
    simp [smul_eq_mul]
  have hint : Integrable (X 0) ℙ := by
    have := (integrable_map_measure (μ := ℙ) (g := fun n : ℕ => (n : ℝ))
      measurable_from_nat.aestronglyMeasurable (haem 0)).mp (by rw [hmap 0]; exact hintpo)
    exact this
  have hmean : ℙ[X 0] = (r : ℝ) := by
    have := integral_map (μ := ℙ) (haem 0) (f := fun n : ℕ => (n : ℝ))
      measurable_from_nat.aestronglyMeasurable
    rw [hmap 0] at this
    show ∫ ω, ((Y 0 ω : ℕ) : ℝ) ∂ℙ = (r : ℝ)
    rw [← this, integral_poissonMeasure' hintpo]
    exact hpo.tsum_eq
  have hslln := strong_law_ae_real X hint hindep hident
  rw [hmean] at hslln
  -- telescoping
  have htel : ∀ ω n, ∑ k ∈ Finset.range n, X k ω = (E i (n : ℝ) ω : ℝ) := by
    intro ω n
    have hle : ∀ k : ℕ, E i (k : ℝ) ω ≤ E i ((k : ℝ) + 1) ω := fun k => hEmono ω (by linarith)
    have : ∀ k ∈ Finset.range n, X k ω = (E i ((k + 1 : ℕ) : ℝ) ω : ℝ) - (E i (k : ℝ) ω : ℝ) := by
      intro k _
      simp only [hX, hY]
      rw [Nat.cast_sub (hle k)]
      push_cast
      ring
    rw [Finset.sum_congr rfl this,
      Finset.sum_range_sub (fun k : ℕ => (E i (k : ℝ) ω : ℝ)) n]
    simp [hE0 ω]
  -- interpolation
  have hgood : ∀ᵐ ω, Tendsto (fun t : ℝ => (E i t ω : ℝ) / t) atTop (𝓝 (r : ℝ)) := by
    filter_upwards [hslln] with ω hω
    simp only [htel ω] at hω
    have hω1 : Tendsto (fun n : ℕ => (E i ((n + 1 : ℕ) : ℝ) ω : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop
        (𝓝 (r : ℝ)) := hω.comp (tendsto_add_atTop_nat 1)
    have hlow : Tendsto (fun n : ℕ => (E i (n : ℝ) ω : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 (r : ℝ)) := by
      have h1 : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 1) :=
        tendsto_natCast_div_add_atTop (1 : ℝ)
      have := hω.mul h1
      rw [mul_one] at this
      refine this.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have : (0 : ℝ) < n := by exact_mod_cast hn
      field_simp
    have hupp : Tendsto (fun n : ℕ => (E i ((n + 1 : ℕ) : ℝ) ω : ℝ) / (n : ℝ)) atTop
        (𝓝 (r : ℝ)) := by
      have h1 : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
        have h2 : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
          tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
        rw [add_zero] at h2
        refine h2.congr' ?_
        filter_upwards [eventually_ge_atTop 1] with n hn
        have : (0 : ℝ) < n := by exact_mod_cast hn
        push_cast
        field_simp
      have := hω1.mul h1
      rw [mul_one] at this
      refine this.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have : (0 : ℝ) < n := by exact_mod_cast hn
      push_cast
      field_simp
    have hfl : Tendsto (fun t : ℝ => ⌊t⌋₊) atTop atTop := tendsto_nat_floor_atTop
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlow.comp hfl) (hupp.comp hfl) ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      simp only [Function.comp]
      have hn1 : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith)
      have hn2 : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
      have htpos : 0 < t := by linarith
      have hE : (E i (⌊t⌋₊ : ℝ) ω : ℝ) ≤ (E i t ω : ℝ) := by exact_mod_cast hEmono ω hn1
      calc (E i (⌊t⌋₊ : ℝ) ω : ℝ) / ((⌊t⌋₊ : ℝ) + 1)
          ≤ (E i (⌊t⌋₊ : ℝ) ω : ℝ) / t :=
            div_le_div_of_nonneg_left (Nat.cast_nonneg _) htpos hn2.le
        _ ≤ (E i t ω : ℝ) / t := div_le_div_of_nonneg_right hE htpos.le
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      simp only [Function.comp]
      have hn2 : t ≤ ((⌊t⌋₊ + 1 : ℕ) : ℝ) := by push_cast; exact (Nat.lt_floor_add_one t).le
      have hn1 : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith)
      have hnpos : (0 : ℝ) < ⌊t⌋₊ := by
        have : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by simpa using ht)
        exact_mod_cast this
      have hE : (E i t ω : ℝ) ≤ (E i ((⌊t⌋₊ + 1 : ℕ) : ℝ) ω : ℝ) := by exact_mod_cast hEmono ω hn2
      calc (E i t ω : ℝ) / t ≤ (E i ((⌊t⌋₊ + 1 : ℕ) : ℝ) ω : ℝ) / t :=
            div_le_div_of_nonneg_right hE (by linarith)
        _ ≤ (E i ((⌊t⌋₊ + 1 : ℕ) : ℝ) ω : ℝ) / (⌊t⌋₊ : ℝ) :=
            div_le_div_of_nonneg_left (Nat.cast_nonneg _) hnpos hn1
  -- conclude: the set has full measure
  have huniv : ℙ (Set.univ : Set Ω) = 1 := by
    have := Measure.map_apply_of_aemeasurable (haem 0) MeasurableSet.univ
    rw [hmap 0, measure_univ, Set.preimage_univ] at this
    exact this.symm
  set S := {ω | Tendsto (fun t : ℝ => (E i t ω : ℝ) / t) atTop (nhds (lam i : ℝ))} with hS
  have hSc : ℙ Sᶜ = 0 := ae_iff.mp hgood
  refine le_antisymm (huniv ▸ measure_mono (Set.subset_univ _)) ?_
  have := measure_univ_le_add_compl (μ := ℙ) S
  rw [hSc, add_zero, huniv] at this
  exact this


