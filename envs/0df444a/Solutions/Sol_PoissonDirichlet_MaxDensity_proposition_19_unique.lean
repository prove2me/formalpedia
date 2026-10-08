-- Prove2me | solution 1 for PoissonDirichlet.MaxDensity.proposition_19_unique
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T15:59:28.618981+00:00
-- url     : https://prove2.me/submissions/596647bc-66d1-4c11-a5be-6d3680d602f6

import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology


namespace PoissonDirichlet.MaxDensity

/-- Key inductive step: agreement on `Ico (1/(n+1)) 1` for all `θ`. -/
theorem p19u_ind (α : ℝ) (hα : 0 ≤ α) (hα1 : α < 1)
    (ν₁ ν₂ : ℝ → Measure ℝ)
    (h₁ : ∀ θ : ℝ, -α < θ →
      IsProbabilityMeasure (ν₁ θ) ∧ ν₁ θ (Set.Ioo (0 : ℝ) 1)ᶜ = 0 ∧
        ∀ s : Set ℝ, MeasurableSet s → s ⊆ Set.Ioo (0 : ℝ) 1 →
          ν₁ θ s = ∫⁻ x in s, ENNReal.ofReal
            (Real.Gamma (θ + 1) / (Real.Gamma (θ + α) * Real.Gamma (1 - α))
              * x ^ (-α - 1) * (1 - x) ^ (α + θ - 1)
              * (ν₁ (α + θ) (Set.Iio (x / (1 - x)))).toReal))
    (h₂ : ∀ θ : ℝ, -α < θ →
      IsProbabilityMeasure (ν₂ θ) ∧ ν₂ θ (Set.Ioo (0 : ℝ) 1)ᶜ = 0 ∧
        ∀ s : Set ℝ, MeasurableSet s → s ⊆ Set.Ioo (0 : ℝ) 1 →
          ν₂ θ s = ∫⁻ x in s, ENNReal.ofReal
            (Real.Gamma (θ + 1) / (Real.Gamma (θ + α) * Real.Gamma (1 - α))
              * x ^ (-α - 1) * (1 - x) ^ (α + θ - 1)
              * (ν₂ (α + θ) (Set.Iio (x / (1 - x)))).toReal)) :
    ∀ n : ℕ, ∀ θ : ℝ, -α < θ → ∀ s : Set ℝ, MeasurableSet s →
      s ⊆ Set.Ico (1 / ((n : ℝ) + 1)) 1 → ν₁ θ s = ν₂ θ s := by
  intro n
  induction n with
  | zero =>
    intro θ hθ s hs hsub
    have : s = ∅ := by
      apply Set.eq_empty_of_subset_empty
      intro x hx
      have := hsub hx
      simp only [Nat.cast_zero, zero_add, div_one, Set.mem_Ico] at this
      linarith [this.1, this.2]
    simp [this]
  | succ n ih =>
    intro θ hθ s hs hsub
    have hθ' : -α < α + θ := by linarith
    obtain ⟨hp1, hn1, hf1⟩ := h₁ θ hθ
    obtain ⟨hp2, hn2, hf2⟩ := h₂ θ hθ
    obtain ⟨hp1', hn1', _⟩ := h₁ (α + θ) hθ'
    obtain ⟨hp2', hn2', _⟩ := h₂ (α + θ) hθ'
    have hsub' : s ⊆ Set.Ioo 0 1 := by
      intro x hx
      have := hsub hx
      simp only [Set.mem_Ico] at this
      refine ⟨lt_of_lt_of_le (by positivity) this.1, this.2⟩
    rw [hf1 s hs hsub', hf2 s hs hsub']
    apply setLIntegral_congr_fun hs
    intro x hx
    have hx' := hsub hx
    simp only [Set.mem_Ico] at hx'
    have hx1 : x < 1 := hx'.2
    have hxpos : 0 < x := lt_of_lt_of_le (by positivity) hx'.1
    -- y = x/(1-x) ≥ 1/(n+1)
    set y := x / (1 - x) with hy
    have hy1 : 1 / ((n : ℝ) + 1) ≤ y := by
      rw [hy, le_div_iff₀ (by linarith)]
      have h1 : 1 / ((n : ℝ) + 1 + 1) ≤ x := by
        have : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 1 + 1 := by push_cast; ring
        rw [this] at hx'; exact hx'.1
      have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [div_le_iff₀ (by positivity)] at h1
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hn0]
      nlinarith
    -- the measures of Iio y agree
    have key : ν₁ (α + θ) (Set.Iio y) = ν₂ (α + θ) (Set.Iio y) := by
      have hIci : ν₁ (α + θ) (Set.Ici y) = ν₂ (α + θ) (Set.Ici y) := by
        have e1 : ν₁ (α + θ) (Set.Ici y) = ν₁ (α + θ) (Set.Ici y ∩ Set.Ioo 0 1) := by
          rw [← measure_inter_add_diff (Set.Ici y) (measurableSet_Ioo (a := (0:ℝ)) (b := 1))]
          have : ν₁ (α + θ) (Set.Ici y \ Set.Ioo 0 1) = 0 :=
            measure_mono_null (fun z hz => hz.2) hn1'
          rw [this, add_zero]
        have e2 : ν₂ (α + θ) (Set.Ici y) = ν₂ (α + θ) (Set.Ici y ∩ Set.Ioo 0 1) := by
          rw [← measure_inter_add_diff (Set.Ici y) (measurableSet_Ioo (a := (0:ℝ)) (b := 1))]
          have : ν₂ (α + θ) (Set.Ici y \ Set.Ioo 0 1) = 0 :=
            measure_mono_null (fun z hz => hz.2) hn2'
          rw [this, add_zero]
        rw [e1, e2]
        apply ih (α + θ) hθ' _ (measurableSet_Ici.inter measurableSet_Ioo)
        intro z hz
        exact ⟨le_trans hy1 hz.1, hz.2.2⟩
      have c1 : ν₁ (α + θ) (Set.Iio y) + ν₁ (α + θ) (Set.Ici y) = 1 := by
        rw [← measure_union (Set.disjoint_left.2 (fun z hz hz' => by
            simp only [Set.mem_Iio, Set.mem_Ici] at hz hz'; linarith)) measurableSet_Ici,
          Set.Iio_union_Ici, measure_univ]
      have c2 : ν₂ (α + θ) (Set.Iio y) + ν₂ (α + θ) (Set.Ici y) = 1 := by
        rw [← measure_union (Set.disjoint_left.2 (fun z hz hz' => by
            simp only [Set.mem_Iio, Set.mem_Ici] at hz hz'; linarith)) measurableSet_Ici,
          Set.Iio_union_Ici, measure_univ]
      have f1 : ν₁ (α + θ) (Set.Ici y) ≠ ⊤ := measure_ne_top _ _
      have f2 : ν₂ (α + θ) (Set.Ici y) ≠ ⊤ := measure_ne_top _ _
      rw [hIci] at c1
      exact WithTop.add_right_cancel f2 (c1.trans c2.symm)
    show ENNReal.ofReal (_ * (ν₁ (α + θ) (Set.Iio (x / (1 - x)))).toReal) = ENNReal.ofReal (_ * (ν₂ (α + θ) (Set.Iio (x / (1 - x)))).toReal)
    rw [← hy, key]

theorem proposition_19_unique_core (α : ℝ) (hα : 0 ≤ α) (hα1 : α < 1)
    (ν₁ ν₂ : ℝ → Measure ℝ)
    (h₁ : ∀ θ : ℝ, -α < θ →
      IsProbabilityMeasure (ν₁ θ) ∧ ν₁ θ (Set.Ioo (0 : ℝ) 1)ᶜ = 0 ∧
        ∀ s : Set ℝ, MeasurableSet s → s ⊆ Set.Ioo (0 : ℝ) 1 →
          ν₁ θ s = ∫⁻ x in s, ENNReal.ofReal
            (Real.Gamma (θ + 1) / (Real.Gamma (θ + α) * Real.Gamma (1 - α))
              * x ^ (-α - 1) * (1 - x) ^ (α + θ - 1)
              * (ν₁ (α + θ) (Set.Iio (x / (1 - x)))).toReal))
    (h₂ : ∀ θ : ℝ, -α < θ →
      IsProbabilityMeasure (ν₂ θ) ∧ ν₂ θ (Set.Ioo (0 : ℝ) 1)ᶜ = 0 ∧
        ∀ s : Set ℝ, MeasurableSet s → s ⊆ Set.Ioo (0 : ℝ) 1 →
          ν₂ θ s = ∫⁻ x in s, ENNReal.ofReal
            (Real.Gamma (θ + 1) / (Real.Gamma (θ + α) * Real.Gamma (1 - α))
              * x ^ (-α - 1) * (1 - x) ^ (α + θ - 1)
              * (ν₂ (α + θ) (Set.Iio (x / (1 - x)))).toReal)) :
    ∀ θ : ℝ, -α < θ → ν₁ θ = ν₂ θ := by
  intro θ hθ
  have hind := p19u_ind α hα hα1 ν₁ ν₂ h₁ h₂
  obtain ⟨_, hn1, _⟩ := h₁ θ hθ
  obtain ⟨_, hn2, _⟩ := h₂ θ hθ
  ext s hs
  have e1 : ν₁ θ s = ν₁ θ (s ∩ Set.Ioo 0 1) := by
    rw [← measure_inter_add_diff s (measurableSet_Ioo (a := (0:ℝ)) (b := 1))]
    have : ν₁ θ (s \ Set.Ioo 0 1) = 0 := measure_mono_null (fun z hz => hz.2) hn1
    rw [this, add_zero]
  have e2 : ν₂ θ s = ν₂ θ (s ∩ Set.Ioo 0 1) := by
    rw [← measure_inter_add_diff s (measurableSet_Ioo (a := (0:ℝ)) (b := 1))]
    have : ν₂ θ (s \ Set.Ioo 0 1) = 0 := measure_mono_null (fun z hz => hz.2) hn2
    rw [this, add_zero]
  rw [e1, e2]
  have hU : s ∩ Set.Ioo 0 1 = ⋃ n : ℕ, s ∩ Set.Ico (1 / ((n : ℝ) + 1)) 1 := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_iUnion, Set.mem_Ico]
    constructor
    · rintro ⟨hx, h0, h1⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt h0
      exact ⟨n, hx, hn.le, h1⟩
    · rintro ⟨n, hx, h0, h1⟩
      exact ⟨hx, lt_of_lt_of_le (by positivity) h0, h1⟩
  have hmono : Monotone (fun n : ℕ => s ∩ Set.Ico (1 / ((n : ℝ) + 1)) 1) := by
    intro a b hab x hx
    refine ⟨hx.1, le_trans ?_ hx.2.1, hx.2.2⟩
    apply one_div_le_one_div_of_le (by positivity)
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  rw [hU, hmono.measure_iUnion, hmono.measure_iUnion]
  congr 1
  ext n
  exact hind n θ hθ _ (hs.inter measurableSet_Ico) (fun x hx => hx.2)

end PoissonDirichlet.MaxDensity

open PoissonDirichlet.MaxDensity


theorem solution (α : ℝ) (hα : 0 ≤ α) (hα1 : α < 1)
    (ν₁ ν₂ : ℝ → Measure ℝ)
    (h₁ : ∀ θ : ℝ, -α < θ →
      IsProbabilityMeasure (ν₁ θ) ∧ ν₁ θ (Set.Ioo (0 : ℝ) 1)ᶜ = 0 ∧
        ∀ s : Set ℝ, MeasurableSet s → s ⊆ Set.Ioo (0 : ℝ) 1 →
          ν₁ θ s = ∫⁻ x in s, ENNReal.ofReal
            (Real.Gamma (θ + 1) / (Real.Gamma (θ + α) * Real.Gamma (1 - α))
              * x ^ (-α - 1) * (1 - x) ^ (α + θ - 1)
              * (ν₁ (α + θ) (Set.Iio (x / (1 - x)))).toReal))
    (h₂ : ∀ θ : ℝ, -α < θ →
      IsProbabilityMeasure (ν₂ θ) ∧ ν₂ θ (Set.Ioo (0 : ℝ) 1)ᶜ = 0 ∧
        ∀ s : Set ℝ, MeasurableSet s → s ⊆ Set.Ioo (0 : ℝ) 1 →
          ν₂ θ s = ∫⁻ x in s, ENNReal.ofReal
            (Real.Gamma (θ + 1) / (Real.Gamma (θ + α) * Real.Gamma (1 - α))
              * x ^ (-α - 1) * (1 - x) ^ (α + θ - 1)
              * (ν₂ (α + θ) (Set.Iio (x / (1 - x)))).toReal)) :
    ∀ θ : ℝ, -α < θ → ν₁ θ = ν₂ θ := by
  exact proposition_19_unique_core α hα hα1 ν₁ ν₂ h₁ h₂
